// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Packed arrays accessed per element -> unpacked tables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Soa
//
// A packed array that is only ever read and written one element at a time
// (q[i], q[i].field, row[e][bit]) is stored by Verilator as one wide vector.
// Every access is then a bit extract, and a counted loop over the array is
// unrolled into N copies of that extract. On a design the size of an OoO
// core that is about a megabyte of distinct text per simulated cycle.
//
// This pass rewrites those arrays as unpacked element tables:
//
//     logic [N-1:0][W-1:0] mem;          // one VlWide
//     mem[i] <= mem[i] + 1;
//  ->
//     logic [W-1:0] mem [0:N-1];         // mem[i] is one C array load
//
// Clocked loops that scan a converted table with a constant trip count are
// marked on their index variable (soaNoUnroll). V3Unroll leaves them as one
// loop. Non-blocking assigns to the table from inside that loop are committed
// by V3Delayed as a shadow table, which is O(N) instead of the single-slot
// __Vdlyvdim path (that path cannot record more than one index).
//
// Whole-vector operations (assign, compare, pass to a task) keep the variable
// packed. Little-endian ranges and public/port/split_var variables are left
// alone. Combinational loops are still unrolled so V3SplitVar can cut them.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Soa.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct LsbParts final {
    bool indexConst = false;
    int indexVal = 0;
    AstNodeExpr* indexp = nullptr;  // Variable index, still in the tree
    bool offConst = true;
    int offVal = 0;
    AstNodeExpr* offp = nullptr;  // Variable offset within the element
    bool ok = false;
};

AstNodeExpr* peelCast(AstNodeExpr* nodep) {
    while (nodep) {
        if (AstExtend* const extp = VN_CAST(nodep, Extend)) {
            nodep = extp->lhsp();
        } else if (AstExtendS* const extp = VN_CAST(nodep, ExtendS)) {
            nodep = extp->lhsp();
        } else if (AstCCast* const castp = VN_CAST(nodep, CCast)) {
            nodep = castp->lhsp();
        } else {
            break;
        }
    }
    return nodep;
}

// SEL(expr, 0, w) is a truncation inserted so the scaled index fits the
// address width. It does not change which element is selected.
AstNodeExpr* peelTrunc(AstNodeExpr* nodep) {
    nodep = peelCast(nodep);
    if (AstSel* const selp = VN_CAST(nodep, Sel)) {
        const AstConst* const lsbp = VN_CAST(peelCast(selp->lsbp()), Const);
        if (lsbp && lsbp->isZero()) return peelCast(selp->fromp());
    }
    return nodep;
}

bool asScaledIndex(AstNodeExpr* nodep, int elwidth, AstNodeExpr*& idxp) {
    nodep = peelTrunc(nodep);
    AstNodeExpr* lhsp = nullptr;
    AstNodeExpr* rhsp = nullptr;
    if (AstMul* const mulp = VN_CAST(nodep, Mul)) {
        lhsp = mulp->lhsp();
        rhsp = mulp->rhsp();
    } else if (AstMulS* const mulp = VN_CAST(nodep, MulS)) {
        lhsp = mulp->lhsp();
        rhsp = mulp->rhsp();
    } else if (AstShiftL* const shiftp = VN_CAST(nodep, ShiftL)) {
        // i << log2(elwidth) is the same scale as i * elwidth.
        const AstConst* const amt = VN_CAST(peelCast(shiftp->rhsp()), Const);
        if (!amt || amt->toSInt() < 0 || amt->toSInt() >= 31) return false;
        if ((1 << amt->toSInt()) != elwidth) return false;
        idxp = peelCast(shiftp->lhsp());
        return true;
    } else {
        return false;
    }
    const AstConst* const clp = VN_CAST(peelCast(lhsp), Const);
    const AstConst* const crp = VN_CAST(peelCast(rhsp), Const);
    if (clp && clp->toSInt() == elwidth) {
        idxp = peelCast(rhsp);
        return true;
    }
    if (crp && crp->toSInt() == elwidth) {
        idxp = peelCast(lhsp);
        return true;
    }
    return false;
}

bool splitLsb(AstNodeExpr* lsbp, int elwidth, LsbParts& part) {
    AstNodeExpr* const nodep = peelTrunc(lsbp);
    AstNodeExpr* idxp = nullptr;
    if (asScaledIndex(nodep, elwidth, idxp)) {
        part.indexConst = false;
        part.indexp = idxp;
        part.offConst = true;
        part.offVal = 0;
        part.ok = true;
        return true;
    }
    if (AstConst* const constp = VN_CAST(nodep, Const)) {
        const int k = constp->toSInt();
        if (k < 0) return false;
        part.indexConst = true;
        part.indexVal = k / elwidth;
        part.offConst = true;
        part.offVal = k % elwidth;
        part.ok = true;
        return true;
    }
    AstNodeExpr* ap = nullptr;
    AstNodeExpr* bp = nullptr;
    AstAdd* const addp = VN_CAST(nodep, Add);
    if (!addp) return false;
    ap = peelTrunc(addp->lhsp());
    bp = peelTrunc(addp->rhsp());
    AstNodeExpr* otherp = nullptr;
    AstNodeExpr* restp = nullptr;
    if (asScaledIndex(ap, elwidth, otherp)) {
        restp = bp;
    } else if (asScaledIndex(bp, elwidth, otherp)) {
        restp = ap;
    } else {
        return false;
    }
    part.indexConst = false;
    part.indexp = otherp;
    if (AstConst* const offp = VN_CAST(restp, Const)) {
        if (offp->toSInt() < 0) return false;
        part.offConst = true;
        part.offVal = offp->toSInt();
    } else {
        part.offConst = false;
        part.offp = restp;
    }
    part.ok = true;
    return true;
}

bool partsFit(const LsbParts& part, int elwidth, int selWidth) {
    if (selWidth <= 0 || selWidth > elwidth) return false;
    if (!part.offConst) return true;
    if (part.offVal < 0) return false;
    return part.offVal + selWidth <= elwidth;
}

AstNodeExpr* sizedConst(FileLine* fl, int value) {
    // Width commit has already run, so width must equal widthMin.
    return new AstConst{fl, AstConst::WidthedValue{}, 32, static_cast<uint32_t>(value)};
}

AstNodeExpr* indexExpr(FileLine* fl, const LsbParts& part) {
    if (part.indexConst) return sizedConst(fl, part.indexVal);
    return part.indexp->cloneTree(false);
}

AstNodeExpr* offsetExpr(FileLine* fl, const LsbParts& part) {
    if (part.offConst) return sizedConst(fl, part.offVal);
    return part.offp->cloneTree(false);
}

bool varBlocked(const AstVar* varp) {
    if (varp->isIO()) return true;
    if (varp->isPrimaryIO()) return true;
    if (varp->isSigPublic() || varp->isSigModPublic()) return true;
    if (varp->isSigUserRdPublic() || varp->isSigUserRWPublic()) return true;
    if (varp->isForceable() || varp->isSc()) return true;
    if (varp->attrSplitVar()) return true;
    if (varp->valuep()) return true;
    if (varp->isParam() || varp->isGenVar()) return true;
    return false;
}

int elementWidth(const AstPackArrayDType* adtypep) {
    const int elements = adtypep->elementsConst();
    if (elements <= 0) return 0;
    if (adtypep->width() % elements != 0) return 0;
    const int elwidth = adtypep->width() / elements;
    // 1-bit flags, host words, and wide packed elements (a struct entry)
    // are all one table slot. The slot type is the existing element dtype.
    if (elwidth <= 0) return 0;
    if (VN_IS(adtypep->subDTypep()->skipRefp(), UnpackArrayDType)) return 0;
    if (adtypep->subDTypep()->skipRefp()->width() != elwidth) return 0;
    return elwidth;
}

class SoaCollectVisitor final : public VNVisitor {
public:
    std::unordered_map<AstVar*, std::vector<AstVarRef*>> refs;
    void visit(AstVarRef* nodep) override { refs[nodep->varp()].push_back(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

class SoaLoopVisitor final : public VNVisitor {
    const std::unordered_set<AstVar*>& m_converted;
    VDouble0& m_loops;

    static bool underClocked(const AstNode* nodep) {
        for (const AstNode* walkp = nodep; walkp; walkp = walkp->backp()) {
            if (const AstAlways* const alwp = VN_CAST(walkp, Always)) {
                return alwp->sensesp() && alwp->sensesp()->hasClocked();
            }
        }
        return false;
    }
    static const AstConst* peeledConst(AstNodeExpr* nodep) {
        return VN_CAST(peelCast(nodep), Const);
    }
    bool bodyUsesConverted(AstNode* nodep) const {
        if (!nodep) return false;
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (m_converted.count(refp->varp())) return true;
        }
        return bodyUsesConverted(nodep->op1p()) || bodyUsesConverted(nodep->op2p())
               || bodyUsesConverted(nodep->op3p()) || bodyUsesConverted(nodep->op4p())
               || bodyUsesConverted(nodep->nextp());
    }
    void consider(AstWhile* nodep) {
        if (!underClocked(nodep)) return;
        if (!bodyUsesConverted(nodep->stmtsp())) {
            UINFO(4, "  SoA loop no table use" << endl);
            return;
        }
        AstAssign* const initp = VN_CAST(nodep->backp(), Assign);
        if (!initp) {
            UINFO(4, "  SoA loop init " << (nodep->backp() ? nodep->backp()->prettyTypeName() : "null")
                                        << endl);
            return;
        }
        AstVarRef* const initRefp = VN_CAST(initp->lhsp(), VarRef);
        const AstConst* const initConstp = peeledConst(initp->rhsp());
        if (!initRefp || !initRefp->varp() || !initConstp) {
            UINFO(4, "  SoA loop init shape" << endl);
            return;
        }
        AstNode* const incNodep = nodep->incsp();
        AstAssign* const incp = VN_CAST(incNodep, Assign);
        if (!incp || incp->nextp()) {
            UINFO(4, "  SoA loop inc " << (incNodep ? incNodep->prettyTypeName() : "null") << endl);
            return;
        }
        AstVarRef* const incRefp = VN_CAST(incp->lhsp(), VarRef);
        if (!incRefp || incRefp->varp() != initRefp->varp()) return;
        AstNodeExpr* const incRhsp = peelCast(incp->rhsp());
        AstNodeExpr* addLp = nullptr;
        AstNodeExpr* addRp = nullptr;
        AstAdd* const addp = VN_CAST(incRhsp, Add);
        if (!addp) {
            UINFO(4, "  SoA loop add " << incRhsp->prettyTypeName() << endl);
            return;
        }
        addLp = addp->lhsp();
        addRp = addp->rhsp();
        const AstConst* stepCp = nullptr;
        AstVarRef* stepVp = VN_CAST(peelCast(addLp), VarRef);
        if (stepVp && stepVp->varp() == initRefp->varp()) {
            stepCp = peeledConst(addRp);
        } else {
            stepVp = VN_CAST(peelCast(addRp), VarRef);
            stepCp = peeledConst(addLp);
        }
        if (!stepVp || stepVp->varp() != initRefp->varp() || !stepCp) {
            UINFO(4, "  SoA loop step" << endl);
            return;
        }
        if (stepCp->toSInt() != 1) {
            UINFO(4, "  SoA loop step val " << stepCp->toSInt() << endl);
            return;
        }
        // `i < N` is sometimes canonicalized to `N > i`.
        AstNodeExpr* condLp = nullptr;
        AstNodeExpr* condRp = nullptr;
        if (AstLt* const ltp = VN_CAST(nodep->condp(), Lt)) {
            condLp = ltp->lhsp();
            condRp = ltp->rhsp();
        } else if (AstLtS* const ltp = VN_CAST(nodep->condp(), LtS)) {
            condLp = ltp->lhsp();
            condRp = ltp->rhsp();
        } else if (AstGt* const gtp = VN_CAST(nodep->condp(), Gt)) {
            condLp = gtp->rhsp();
            condRp = gtp->lhsp();
        } else if (AstGtS* const gtp = VN_CAST(nodep->condp(), GtS)) {
            condLp = gtp->rhsp();
            condRp = gtp->lhsp();
        } else {
            UINFO(4, "  SoA loop cond " << nodep->condp()->prettyTypeName() << endl);
            return;
        }
        AstVarRef* const condVp = VN_CAST(peelCast(condLp), VarRef);
        const AstConst* const boundp = peeledConst(condRp);
        if (!condVp || condVp->varp() != initRefp->varp() || !boundp) {
            UINFO(4, "  SoA loop bound lhs="
                         << (condLp ? condLp->prettyTypeName() : "null")
                         << " rhs=" << (condRp ? condRp->prettyTypeName() : "null") << endl);
            return;
        }
        const int trips = boundp->toSInt() - initConstp->toSInt();
        // Four is enough to beat the unrolled header. A million is a stand-in
        // for "this is not an infinite loop we failed to recognize".
        if (trips < 4 || trips > 1000000) return;
        initRefp->varp()->soaNoUnroll(true);
        ++m_loops;
        UINFO(4, "  SoA keep rolled (" << trips << ") " << nodep << endl);
    }

public:
    SoaLoopVisitor(const std::unordered_set<AstVar*>& converted, VDouble0& loops)
        : m_converted{converted}
        , m_loops{loops} {}
    void visit(AstWhile* nodep) override {
        consider(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

class SoaVisitor final : public VNVisitor {
    VDouble0 m_arrays;
    VDouble0 m_loops;

    bool convert(AstVar* varp, const std::vector<AstVarRef*>& refps) {
        if (varBlocked(varp)) {
            UINFO(4, "  SoA skip blocked " << varp->prettyNameQ() << endl);
            return false;
        }
        const AstPackArrayDType* const adtypep
            = VN_CAST(varp->dtypep()->skipRefp(), PackArrayDType);
        if (!adtypep) {
            UINFO(4, "  SoA skip dtype " << varp->prettyNameQ() << " " << varp->dtypep() << endl);
            return false;
        }
        if (!adtypep->rangep() || adtypep->lo() != 0 || adtypep->rangep()->littleEndian()) {
            UINFO(4, "  SoA skip range " << varp->prettyNameQ() << endl);
            return false;
        }
        const int elements = adtypep->elementsConst();
        if (elements < 4) return false;
        const int elwidth = elementWidth(adtypep);
        if (elwidth <= 0) {
            UINFO(4, "  SoA skip width " << varp->prettyNameQ() << endl);
            return false;
        }

        struct Use final {
            AstSel* selp;
            LsbParts parts;
        };
        std::vector<Use> uses;
        uses.reserve(refps.size());
        for (AstVarRef* const refp : refps) {
            AstSel* const selp = VN_CAST(refp->backp(), Sel);
            if (!selp || selp->fromp() != refp) {
                UINFO(4, "  SoA skip ref parent " << refp << " back " << refp->backp() << endl);
                return false;
            }
            if (!VN_IS(selp->widthp(), Const)) return false;
            LsbParts parts;
            if (!splitLsb(selp->lsbp(), elwidth, parts)) {
                UINFO(4, "  SoA skip lsb elw=" << elwidth << endl);
                if (debug() >= 4) selp->dumpTree("-  soa-sel: ");
                return false;
            }
            if (!partsFit(parts, elwidth, selp->widthConst())) {
                UINFO(4, "  SoA skip fit " << selp << endl);
                return false;
            }
            uses.push_back({selp, parts});
        }
        if (uses.empty()) return false;

        FileLine* const fl = varp->fileline();
        AstRange* const rangep = new AstRange{fl, elements - 1, 0};
        AstUnpackArrayDType* const newDtp
            = new AstUnpackArrayDType{fl, adtypep->subDTypep(), rangep};
        v3Global.rootp()->typeTablep()->addTypesp(newDtp);
        varp->dtypep(newDtp);

        for (const Use& use : uses) {
            AstSel* const selp = use.selp;
            FileLine* const sfl = selp->fileline();
            AstNodeExpr* const fromp = selp->fromp()->unlinkFrBack();
            fromp->dtypep(newDtp);
            AstNodeExpr* const idxp = indexExpr(sfl, use.parts);
            AstArraySel* const arrp = new AstArraySel{sfl, fromp, idxp};
            const bool full = use.parts.offConst && use.parts.offVal == 0
                              && selp->widthConst() == elwidth;
            if (full) {
                selp->replaceWith(arrp);
            } else {
                AstNodeExpr* const offp = offsetExpr(sfl, use.parts);
                AstNodeExpr* const widthp = selp->widthp()->unlinkFrBack();
                AstSel* const newSelp = new AstSel{sfl, arrp, offp, widthp};
                newSelp->dtypeFrom(selp);
                selp->replaceWith(newSelp);
            }
            VL_DO_DANGLING(selp->deleteTree(), selp);
        }
        ++m_arrays;
        UINFO(4, "  SoA table " << varp->prettyNameQ() << " [" << elements << "] x " << elwidth
                                << endl);
        return true;
    }

public:
    explicit SoaVisitor(AstNetlist* nodep) {
        SoaCollectVisitor collect;
        collect.iterate(nodep);
        std::unordered_set<AstVar*> converted;
        for (auto& it : collect.refs) {
            if (convert(it.first, it.second)) converted.insert(it.first);
        }
        if (!converted.empty()) {
            SoaLoopVisitor loops{converted, m_loops};
            loops.iterate(nodep);
        }
    }
    ~SoaVisitor() override {
        V3Stats::addStat("Optimizations, SoA arrays converted", m_arrays);
        V3Stats::addStat("Optimizations, SoA loops kept rolled", m_loops);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

}  // namespace

void V3Soa::soaAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SoaVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("soa", 0, dumpTree() >= 6);
}
