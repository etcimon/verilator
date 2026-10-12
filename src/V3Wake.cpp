// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Invert small-tag wakeup compares to a waiter table
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
// V3Wake
//
// A counted entry scan whose body is a counted writeback scan of the form
//
//   if (pred_e[e] && pred_w[w] && tag[e] == key[w]) ready[e] = 1;
//
// compares DEPTH*NR_WB tags. When the tag is a few bits wide the same
// function is a bitmask per tag value:
//
//   for e: if (pred_e[e]) table[tag[e]] |= 1 << e;
//   for w: if (pred_w[w]) mask |= table[key[w]];
//   for e: if (mask[e]) ready[e] = 1;
//
// Setting the ready bit is monotonic, so building the table from the
// post-prefix entry state and applying it after the writeback loop matches
// the nested compares. The table is rebuilt each evaluation; dispatch does
// not have to maintain it. DEPTH is at most 64 so the mask is one word, and
// the tag is at most 8 bits so the table stays small.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Wake.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <functional>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

constexpr int kMaxDepth = 64;
constexpr int kMaxTag = 8;

enum class Side : uint8_t { None, Entry, Key, Both };

struct FieldUse final {
    AstVar* varp = nullptr;
    int stride = 0;
    int lsb = 0;
    int width = 0;
};

struct Match final {
    AstNodeExpr* tagp = nullptr;
    AstNodeExpr* keyp = nullptr;
    std::vector<AstNodeExpr*> entryps;
    std::vector<AstNodeExpr*> keyps;
    AstNodeExpr* readyp = nullptr;
    AstNodeExpr* onep = nullptr;
    int tagWidth = 0;
};

AstNodeExpr* peelCast(AstNodeExpr* nodep) {
    for (int guard = 0; nodep && guard < 8; ++guard) {
        if (AstExtend* const extp = VN_CAST(nodep, Extend)) {
            nodep = extp->lhsp();
        } else if (AstExtendS* const extp = VN_CAST(nodep, ExtendS)) {
            nodep = extp->lhsp();
        } else if (AstCCast* const castp = VN_CAST(nodep, CCast)) {
            nodep = castp->lhsp();
        } else if (AstCast* const castp = VN_CAST(nodep, Cast)) {
            nodep = castp->fromp();
        } else {
            break;
        }
    }
    return nodep;
}

bool constUInt(AstNodeExpr* nodep, uint32_t& out) {
    const AstConst* const cp = VN_CAST(peelCast(nodep), Const);
    if (!cp || cp->num().isFourState() || cp->num().isDouble() || cp->num().isString()) return false;
    if (cp->width() > 32) {
        if (cp->width() > 64 || cp->toUQuad() > 0xffffffffULL) return false;
    }
    out = cp->toUInt();
    return true;
}

AstVar* peelVar(AstNodeExpr* nodep) {
    for (int guard = 0; nodep && guard < 8; ++guard) {
        nodep = peelCast(nodep);
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp->varp();
        AstSel* const selp = VN_CAST(nodep, Sel);
        if (!selp) return nullptr;
        uint32_t lsb = 0;
        if (!constUInt(selp->lsbp(), lsb) || lsb != 0) return nullptr;
        nodep = selp->fromp();
    }
    return nullptr;
}

void childWalk(AstNode* nodep, const std::function<void(AstNode*)>& fn) {
    if (!nodep) return;
    fn(nodep->op1p());
    fn(nodep->op2p());
    fn(nodep->op3p());
    fn(nodep->op4p());
}

void noteIdx(AstNode* nodep, AstVar* entryp, AstVar* keyp, bool& hasE, bool& hasK) {
    if (!nodep || (hasE && hasK)) return;
    if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
        if (refp->varp() == entryp) hasE = true;
        if (refp->varp() == keyp) hasK = true;
    }
    childWalk(nodep, [&](AstNode* childp) { noteIdx(childp, entryp, keyp, hasE, hasK); });
}

Side classify(AstNode* nodep, AstVar* entryp, AstVar* keyp) {
    bool hasE = false;
    bool hasK = false;
    noteIdx(nodep, entryp, keyp, hasE, hasK);
    if (hasE && hasK) return Side::Both;
    if (hasE) return Side::Entry;
    if (hasK) return Side::Key;
    return Side::None;
}

bool asAnd(AstNodeExpr* nodep, AstNodeExpr*& ap, AstNodeExpr*& bp) {
    if (AstAnd* const andp = VN_CAST(nodep, And)) {
        ap = andp->lhsp();
        bp = andp->rhsp();
        return true;
    }
    if (AstLogAnd* const andp = VN_CAST(nodep, LogAnd)) {
        ap = andp->lhsp();
        bp = andp->rhsp();
        return true;
    }
    return false;
}

void flattenAnd(AstNodeExpr* nodep, std::vector<AstNodeExpr*>& terms) {
    nodep = peelCast(nodep);
    if (!nodep) return;
    AstNodeExpr* ap = nullptr;
    AstNodeExpr* bp = nullptr;
    if (nodep->width() == 1 && asAnd(nodep, ap, bp)) {
        flattenAnd(ap, terms);
        flattenAnd(bp, terms);
        return;
    }
    terms.push_back(nodep);
}

// lsb = offset + index * stride, with truncating selects and zero-extends.
bool parseAffine(AstNodeExpr* nodep, AstVar* idxp, int& offset, int& stride, bool& sawIdx) {
    nodep = peelCast(nodep);
    if (!nodep) return false;
    if (AstSel* const selp = VN_CAST(nodep, Sel)) {
        uint32_t lsb = 0;
        if (!constUInt(selp->lsbp(), lsb) || lsb != 0) return false;
        return parseAffine(selp->fromp(), idxp, offset, stride, sawIdx);
    }
    if (AstAdd* const addp = VN_CAST(nodep, Add)) {
        uint32_t cval = 0;
        if (constUInt(addp->lhsp(), cval) && cval <= 0x00ffffffU) {
            offset += static_cast<int>(cval);
            return parseAffine(addp->rhsp(), idxp, offset, stride, sawIdx);
        }
        if (constUInt(addp->rhsp(), cval) && cval <= 0x00ffffffU) {
            offset += static_cast<int>(cval);
            return parseAffine(addp->lhsp(), idxp, offset, stride, sawIdx);
        }
        return false;
    }
    if (AstMul* const mulp = VN_CAST(nodep, Mul)) {
        uint32_t cval = 0;
        AstNodeExpr* otherp = nullptr;
        if (constUInt(mulp->lhsp(), cval)) {
            otherp = mulp->rhsp();
        } else if (constUInt(mulp->rhsp(), cval)) {
            otherp = mulp->lhsp();
        } else {
            return false;
        }
        if (sawIdx || peelVar(otherp) != idxp || cval == 0 || cval > 0x00ffffffU) return false;
        sawIdx = true;
        stride = static_cast<int>(cval);
        return true;
    }
    if (AstShiftL* const shiftp = VN_CAST(nodep, ShiftL)) {
        uint32_t cval = 0;
        if (!constUInt(shiftp->rhsp(), cval) || cval >= 31) return false;
        if (sawIdx || peelVar(shiftp->lhsp()) != idxp) return false;
        sawIdx = true;
        stride = 1 << cval;
        return true;
    }
    if (peelVar(nodep) == idxp) {
        if (sawIdx) return false;
        sawIdx = true;
        stride = 1;
        return true;
    }
    return false;
}

bool parseSelField(AstNodeExpr* exprp, AstVar* idxp, FieldUse& field) {
    exprp = peelCast(exprp);
    AstSel* const selp = VN_CAST(exprp, Sel);
    if (!selp) return false;
    AstVarRef* const refp = VN_CAST(peelCast(selp->fromp()), VarRef);
    uint32_t width = 0;
    if (!refp || !refp->varp() || !constUInt(selp->widthp(), width) || width == 0) return false;
    int offset = 0;
    int stride = 0;
    bool sawIdx = false;
    if (!parseAffine(selp->lsbp(), idxp, offset, stride, sawIdx) || !sawIdx) return false;
    field.varp = refp->varp();
    field.stride = stride;
    field.lsb = offset;
    field.width = static_cast<int>(width);
    return true;
}

int tagWidthOf(AstNodeExpr* exprp) {
    exprp = peelCast(exprp);
    if (AstSel* const selp = VN_CAST(exprp, Sel)) {
        uint32_t width = 0;
        if (constUInt(selp->widthp(), width) && width >= 1 && width <= static_cast<uint32_t>(kMaxTag)) {
            return static_cast<int>(width);
        }
    }
    const int width = exprp ? exprp->width() : 0;
    if (width >= 1 && width <= kMaxTag) return width;
    return -1;
}

AstNode* onlyStmt(AstNode* stmtp) {
    if (!stmtp || stmtp->nextp()) return nullptr;
    if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) return onlyStmt(beginp->stmtsp());
    return stmtp;
}

bool matchCount(AstWhile* nodep, AstVar*& idxp, int& trips) {
    AstAssign* const initp = VN_CAST(nodep->backp(), Assign);
    if (!initp || initp->nextp() != nodep) return false;
    idxp = peelVar(initp->lhsp());
    uint32_t initVal = 0;
    if (!idxp || !constUInt(initp->rhsp(), initVal) || initVal != 0) return false;
    AstAssign* const incp = VN_CAST(nodep->incsp(), Assign);
    if (!incp || incp->nextp() || peelVar(incp->lhsp()) != idxp) return false;
    AstAdd* const addp = VN_CAST(peelCast(incp->rhsp()), Add);
    if (!addp) return false;
    AstNodeExpr* stepExprp = nullptr;
    if (peelVar(addp->lhsp()) == idxp) {
        stepExprp = addp->rhsp();
    } else if (peelVar(addp->rhsp()) == idxp) {
        stepExprp = addp->lhsp();
    } else {
        return false;
    }
    uint32_t step = 0;
    if (!constUInt(stepExprp, step) || step != 1) return false;

    AstNodeExpr* varSide = nullptr;
    AstNodeExpr* boundSide = nullptr;
    if (AstLt* const ltp = VN_CAST(nodep->condp(), Lt)) {
        varSide = ltp->lhsp();
        boundSide = ltp->rhsp();
    } else if (AstLtS* const ltp = VN_CAST(nodep->condp(), LtS)) {
        varSide = ltp->lhsp();
        boundSide = ltp->rhsp();
    } else if (AstGt* const gtp = VN_CAST(nodep->condp(), Gt)) {
        varSide = gtp->rhsp();
        boundSide = gtp->lhsp();
    } else if (AstGtS* const gtp = VN_CAST(nodep->condp(), GtS)) {
        varSide = gtp->rhsp();
        boundSide = gtp->lhsp();
    } else {
        return false;
    }
    if (peelVar(varSide) != idxp) return false;
    uint32_t bound = 0;
    if (!constUInt(boundSide, bound) || bound < 1 || bound > 1000000U) return false;
    trips = static_cast<int>(bound);
    return true;
}

AstNodeModule* moduleOf(AstNode* nodep) {
    while (nodep) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) return modp;
        while (nodep->backp() && nodep->backp()->nextp() == nodep) nodep = nodep->backp();
        nodep = nodep->backp();
    }
    return nullptr;
}

AstNodeExpr* constU32(FileLine* fl, uint32_t value) {
    return new AstConst{fl, AstConst::WidthedValue{}, 32, value};
}

AstNode* countedLike(AstWhile* srcp, AstNode* bodyp) {
    AstAssign* const initp = VN_CAST(srcp->backp(), Assign);
    if (!initp || !srcp->condp() || !srcp->incsp() || !bodyp) return nullptr;
    AstAssign* const initc = initp->cloneTree(false);
    AstWhile* const loopp = new AstWhile{srcp->fileline(), srcp->condp()->cloneTree(false), bodyp,
                                         srcp->incsp()->cloneTree(false)};
    AstNode* const headp = initc;
    headp->addNext(loopp);
    return headp;
}

class WakeVisitor final : public VNVisitor {
    std::vector<AstWhile*> m_whiles;
    std::vector<Match> m_matches;
    std::vector<FieldUse> m_writes;
    AstVar* m_entryp = nullptr;
    AstVar* m_keyp = nullptr;
    int m_seq = 0;
    VDouble0 m_nests;

    bool rangesOverlap(const FieldUse& a, const FieldUse& b) const {
        if (a.varp != b.varp) return false;
        if (a.stride != b.stride) return true;
        return a.lsb < b.lsb + b.width && b.lsb < a.lsb + a.width;
    }

    bool isWrittenVar(AstVar* varp) const {
        for (const FieldUse& wr : m_writes) {
            if (wr.varp == varp) return true;
        }
        return false;
    }

    bool overlaps(AstNode* nodep) {
        if (!nodep) return false;
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            FieldUse field;
            if (parseSelField(selp, m_entryp, field)) {
                for (const FieldUse& wr : m_writes) {
                    if (rangesOverlap(field, wr)) return true;
                }
                return overlaps(selp->lsbp()) || overlaps(selp->widthp());
            }
        }
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (isWrittenVar(refp->varp())) return true;
        }
        return overlaps(nodep->op1p()) || overlaps(nodep->op2p()) || overlaps(nodep->op3p())
               || overlaps(nodep->op4p());
    }

    // One statement. The caller walks the list; following nextp would re-enter
    // the wakeup nest this prefix sits beside.
    bool stmtBad(AstNode* stp) {
        if (!stp) return false;
        if (AstAssign* const ap = VN_CAST(stp, Assign)) {
            if (overlaps(ap->rhsp())) return true;
            FieldUse field;
            if (parseSelField(ap->lhsp(), m_entryp, field)) {
                for (const FieldUse& wr : m_writes) {
                    if (rangesOverlap(field, wr)) return true;
                }
            } else if (overlaps(ap->lhsp())) {
                return true;
            }
            return false;
        }
        if (AstIf* const ifp = VN_CAST(stp, If)) {
            if (overlaps(ifp->condp())) return true;
            for (AstNode* thenp = ifp->thensp(); thenp; thenp = thenp->nextp()) {
                if (stmtBad(thenp)) return true;
            }
            for (AstNode* elsep = ifp->elsesp(); elsep; elsep = elsep->nextp()) {
                if (stmtBad(elsep)) return true;
            }
            return false;
        }
        return overlaps(stp);
    }

    bool addMatch(AstIf* ifp, std::vector<AstNodeExpr*> entryps, std::vector<AstNodeExpr*> keyps) {
        std::vector<AstNodeExpr*> terms;
        flattenAnd(ifp->condp(), terms);
        AstNodeExpr* eqExprp = nullptr;
        for (AstNodeExpr* termp : terms) {
            AstNodeExpr* const peeled = peelCast(termp);
            if (VN_IS(peeled, Eq)) {
                if (eqExprp) return false;
                eqExprp = peeled;
            } else {
                const Side side = classify(termp, m_entryp, m_keyp);
                if (side == Side::Both) return false;
                if (side == Side::Entry) {
                    entryps.push_back(termp);
                } else {
                    keyps.push_back(termp);
                }
            }
        }
        AstEq* const eqp = VN_CAST(eqExprp, Eq);
        if (!eqp) {
            UINFO(4, "  Wake match no eq" << endl);
            return false;
        }
        const Side left = classify(eqp->lhsp(), m_entryp, m_keyp);
        const Side right = classify(eqp->rhsp(), m_entryp, m_keyp);
        AstNodeExpr* tagp = nullptr;
        AstNodeExpr* keyExprp = nullptr;
        if (left == Side::Entry && right == Side::Key) {
            tagp = eqp->lhsp();
            keyExprp = eqp->rhsp();
        } else if (left == Side::Key && right == Side::Entry) {
            tagp = eqp->rhsp();
            keyExprp = eqp->lhsp();
        } else {
            UINFO(4, "  Wake eq sides" << endl);
            return false;
        }
        const int tw = tagWidthOf(tagp);
        if (tw < 1) {
            UINFO(4, "  Wake tag width " << (tagp ? tagp->width() : -1) << endl);
            return false;
        }
        AstAssign* const asgp = VN_CAST(onlyStmt(ifp->thensp()), Assign);
        if (!asgp || !asgp->rhsp()->isOne() || asgp->lhsp()->width() != 1) {
            UINFO(4, "  Wake match assign" << endl);
            return false;
        }
        if (classify(asgp->lhsp(), m_entryp, m_keyp) != Side::Entry) {
            UINFO(4, "  Wake match lhs side" << endl);
            return false;
        }
        FieldUse wr;
        if (!parseSelField(asgp->lhsp(), m_entryp, wr)) {
            UINFO(4, "  Wake match lhs field" << endl);
            return false;
        }
        m_writes.push_back(wr);
        m_matches.push_back(Match{tagp, keyExprp, entryps, keyps, asgp->lhsp(), asgp->rhsp(), tw});
        return true;
    }

    bool isMatchIf(AstIf* ifp) {
        if (!ifp || ifp->elsesp()) return false;
        if (!VN_IS(onlyStmt(ifp->thensp()), Assign)) return false;
        std::vector<AstNodeExpr*> terms;
        flattenAnd(ifp->condp(), terms);
        int eqs = 0;
        for (AstNodeExpr* termp : terms) {
            if (VN_IS(peelCast(termp), Eq)) ++eqs;
        }
        return eqs == 1;
    }

    bool parseStmts(AstNode* stmtp, std::vector<AstNodeExpr*> entryps,
                    std::vector<AstNodeExpr*> keyps) {
        if (!stmtp) return false;
        for (AstNode* stp = stmtp; stp; stp = stp->nextp()) {
            AstIf* const ifp = VN_CAST(stp, If);
            if (!ifp || ifp->elsesp()) {
                UINFO(4, "  Wake body stmt " << (stp ? stp->prettyTypeName() : "null") << endl);
                return false;
            }
            if (isMatchIf(ifp)) {
                if (!addMatch(ifp, entryps, keyps)) return false;
            } else {
                const Side side = classify(ifp->condp(), m_entryp, m_keyp);
                if (side == Side::Both) return false;
                std::vector<AstNodeExpr*> nextEntry = entryps;
                std::vector<AstNodeExpr*> nextKey = keyps;
                if (side == Side::Entry) {
                    nextEntry.push_back(ifp->condp());
                } else {
                    nextKey.push_back(ifp->condp());
                }
                if (!parseStmts(ifp->thensp(), nextEntry, nextKey)) return false;
            }
        }
        return true;
    }

    bool findInner(AstWhile* outerp, AstWhile*& innerp, AstIf*& guardp) {
        innerp = nullptr;
        guardp = nullptr;
        int found = 0;
        for (AstNode* stp = outerp->stmtsp(); stp; stp = stp->nextp()) {
            AstWhile* candp = VN_CAST(stp, While);
            AstIf* candGuard = nullptr;
            if (!candp) {
                AstIf* const ifp = VN_CAST(stp, If);
                if (!ifp || ifp->elsesp()) continue;
                for (AstNode* thenp = ifp->thensp(); thenp; thenp = thenp->nextp()) {
                    if (AstWhile* const wp = VN_CAST(thenp, While)) {
                        if (candp) return false;
                        candp = wp;
                    }
                }
                if (!candp) continue;
                AstNode* const prevp = candp->backp();
                for (AstNode* thenp = ifp->thensp(); thenp; thenp = thenp->nextp()) {
                    if (thenp == candp) continue;
                    if (thenp != prevp || !VN_IS(thenp, Assign)) return false;
                }
                candGuard = ifp;
            }
            ++found;
            innerp = candp;
            guardp = candGuard;
        }
        return found == 1 && innerp;
    }

    AstNodeExpr* combineAnd(FileLine* fl, const std::vector<AstNodeExpr*>& terms) {
        AstNodeExpr* accp = nullptr;
        for (AstNodeExpr* termp : terms) {
            AstNodeExpr* const cloned = termp->cloneTree(false);
            if (!accp) {
                accp = cloned;
            } else {
                accp = new AstAnd{fl, accp, cloned};
                accp->dtypeSetBit();
            }
        }
        return accp;
    }

    AstVar* newWord(AstNodeModule* modp, FileLine* fl, const std::string& name, int width) {
        AstVar* const varp
            = new AstVar{fl, VVarType::MODULETEMP, name, modp->findLogicDType(width, width, VSigning::UNSIGNED)};
        modp->addStmtsp(varp);
        return varp;
    }

    AstVar* newTable(AstNodeModule* modp, FileLine* fl, const std::string& name, int depth,
                     int slots) {
        AstNodeDType* const elemp = modp->findLogicDType(depth, depth, VSigning::UNSIGNED);
        AstUnpackArrayDType* const adtp
            = new AstUnpackArrayDType{fl, elemp, new AstRange{fl, slots - 1, 0}};
        v3Global.rootp()->typeTablep()->addTypesp(adtp);
        AstVar* const varp = new AstVar{fl, VVarType::MODULETEMP, name, adtp};
        modp->addStmtsp(varp);
        return varp;
    }

    AstNode* countedNew(FileLine* fl, AstVar* idxp, int trips, AstNode* bodyp) {
        AstAssign* const initp
            = new AstAssign{fl, new AstVarRef{fl, idxp, VAccess::WRITE}, constU32(fl, 0)};
        AstWhile* const loopp = new AstWhile{
            fl, new AstGt{fl, constU32(fl, static_cast<uint32_t>(trips)),
                          new AstVarRef{fl, idxp, VAccess::READ}},
            bodyp,
            new AstAssign{fl, new AstVarRef{fl, idxp, VAccess::WRITE},
                          new AstAdd{fl, new AstVarRef{fl, idxp, VAccess::READ}, constU32(fl, 1)}}};
        AstAdd* const addp = VN_CAST(loopp->incsp()->op1p(), Add);  // rhsp of the assign is op1
        if (addp) addp->dtypeSetLogicSized(32, VSigning::UNSIGNED);
        AstNode* const headp = initp;
        headp->addNext(loopp);
        return headp;
    }

    AstNode* build(AstWhile* outerp, AstWhile* innerp, int depth) {
        AstNodeModule* const modp = moduleOf(outerp);
        if (!modp) return nullptr;
        FileLine* const fl = outerp->fileline();
        const int id = m_seq++;
        AstVar* const clip = newWord(modp, fl, "__Vwake_i" + cvtToStr(id), 32);

        struct Slot final {
            AstVar* tablep = nullptr;
            AstVar* maskp = nullptr;
        };
        std::vector<Slot> slots;
        slots.reserve(m_matches.size());
        AstNode* listp = nullptr;
        auto append = [&](AstNode* nodep) {
            if (!nodep) return;
            if (!listp) {
                listp = nodep;
            } else {
                listp->addNext(nodep);
            }
        };

        for (size_t i = 0; i < m_matches.size(); ++i) {
            const Match& match = m_matches[i];
            const int slotsN = 1 << match.tagWidth;
            Slot slot;
            slot.tablep = newTable(modp, fl, "__Vwake_t" + cvtToStr(id) + "_" + cvtToStr(i), depth,
                                   slotsN);
            slot.maskp = newWord(modp, fl, "__Vwake_m" + cvtToStr(id) + "_" + cvtToStr(i), depth);
            slots.push_back(slot);
            AstArraySel* const wrp = new AstArraySel{
                fl, new AstVarRef{fl, slot.tablep, VAccess::WRITE},
                new AstVarRef{fl, clip, VAccess::READ}};
            append(countedNew(
                fl, clip, slotsN,
                new AstAssign{fl, wrp, new AstConst{fl, AstConst::WidthedValue{}, depth, 0}}));
        }

        AstNode* fillBody = nullptr;
        for (size_t i = 0; i < m_matches.size(); ++i) {
            const Match& match = m_matches[i];
            AstNodeExpr* const tagRp = match.tagp->cloneTree(false);
            AstNodeExpr* const tagWp = match.tagp->cloneTree(false);
            AstShiftL* const bitp = new AstShiftL{
                fl, new AstConst{fl, AstConst::WidthedValue{}, depth, 1},
                new AstVarRef{fl, m_entryp, VAccess::READ}, depth};
            AstArraySel* const rdp = new AstArraySel{
                fl, new AstVarRef{fl, slots[i].tablep, VAccess::READ}, tagRp};
            AstOr* const orp = new AstOr{fl, rdp, bitp};
            orp->dtypeSetLogicSized(depth, VSigning::UNSIGNED);
            AstAssign* const asgp = new AstAssign{
                fl,
                new AstArraySel{fl, new AstVarRef{fl, slots[i].tablep, VAccess::WRITE}, tagWp},
                orp};
            AstNode* stp = asgp;
            if (AstNodeExpr* const predp = combineAnd(fl, match.entryps)) {
                stp = new AstIf{fl, predp, asgp};
            }
            if (!fillBody) {
                fillBody = stp;
            } else {
                fillBody->addNext(stp);
            }
        }
        append(countedLike(outerp, fillBody));

        AstNode* wakeBody = nullptr;
        for (size_t i = 0; i < m_matches.size(); ++i) {
            const Match& match = m_matches[i];
            append(new AstAssign{fl, new AstVarRef{fl, slots[i].maskp, VAccess::WRITE},
                                 new AstConst{fl, AstConst::WidthedValue{}, depth, 0}});
            AstOr* const orp = new AstOr{
                fl, new AstVarRef{fl, slots[i].maskp, VAccess::READ},
                new AstArraySel{fl, new AstVarRef{fl, slots[i].tablep, VAccess::READ},
                                match.keyp->cloneTree(false)}};
            orp->dtypeSetLogicSized(depth, VSigning::UNSIGNED);
            AstAssign* const asgp
                = new AstAssign{fl, new AstVarRef{fl, slots[i].maskp, VAccess::WRITE}, orp};
            AstNode* stp = asgp;
            if (AstNodeExpr* const predp = combineAnd(fl, match.keyps)) {
                stp = new AstIf{fl, predp, asgp};
            }
            if (!wakeBody) {
                wakeBody = stp;
            } else {
                wakeBody->addNext(stp);
            }
        }
        append(countedLike(innerp, wakeBody));

        AstNode* applyBody = nullptr;
        for (size_t i = 0; i < m_matches.size(); ++i) {
            const Match& match = m_matches[i];
            AstSel* const bitp = new AstSel{fl, new AstVarRef{fl, slots[i].maskp, VAccess::READ},
                                            new AstVarRef{fl, m_entryp, VAccess::READ},
                                            new AstConst{fl, AstConst::WidthedValue{}, 32, 1}};
            AstAssign* const asgp = new AstAssign{fl, match.readyp->cloneTree(false),
                                                  match.onep->cloneTree(false)};
            AstIf* const ifp = new AstIf{fl, bitp, asgp};
            if (!applyBody) {
                applyBody = ifp;
            } else {
                applyBody->addNext(ifp);
            }
        }
        append(countedLike(outerp, applyBody));
        return listp;
    }

    bool tryOuter(AstWhile* outerp) {
        m_matches.clear();
        m_writes.clear();
        m_entryp = nullptr;
        m_keyp = nullptr;
        int depth = 0;
        if (!matchCount(outerp, m_entryp, depth) || depth < 4 || depth > kMaxDepth) {
            UINFO(5, "  Wake no outer count depth=" << depth << endl);
            return false;
        }
        AstWhile* innerp = nullptr;
        AstIf* guardp = nullptr;
        if (!findInner(outerp, innerp, guardp)) {
            UINFO(5, "  Wake no inner" << endl);
            return false;
        }
        int nwb = 0;
        AstVar* keyIdx = nullptr;
        if (!matchCount(innerp, keyIdx, nwb) || keyIdx == m_entryp || nwb < 2 || nwb > kMaxDepth) {
            UINFO(4, "  Wake bad inner nwb=" << nwb << endl);
            return false;
        }
        m_keyp = keyIdx;

        std::vector<AstNodeExpr*> entryps;
        if (guardp) {
            const Side side = classify(guardp->condp(), m_entryp, m_keyp);
            if (side == Side::Key || side == Side::Both) {
                UINFO(4, "  Wake guard side" << endl);
                return false;
            }
            entryps.push_back(guardp->condp());
        }
        if (!parseStmts(innerp->stmtsp(), entryps, {}) || m_matches.empty()) {
            UINFO(4, "  Wake parse matches=" << m_matches.size() << endl);
            return false;
        }
        for (const Match& match : m_matches) {
            // readyp is the bit this match writes, not a value the compare reads.
            if (overlaps(match.tagp) || overlaps(match.keyp)) {
                UINFO(4, "  Wake overlap tag/key" << endl);
                return false;
            }
            for (AstNodeExpr* predp : match.entryps) {
                if (overlaps(predp)) {
                    UINFO(4, "  Wake overlap entry pred" << endl);
                    return false;
                }
            }
            for (AstNodeExpr* predp : match.keyps) {
                if (overlaps(predp)) {
                    UINFO(4, "  Wake overlap key pred" << endl);
                    return false;
                }
            }
        }
        AstNode* const skipp = guardp ? static_cast<AstNode*>(guardp) : static_cast<AstNode*>(innerp);
        AstNode* const initSkip = VN_CAST(innerp->backp(), Assign);
        for (AstNode* stp = outerp->stmtsp(); stp; stp = stp->nextp()) {
            if (stp == skipp || stp == initSkip) continue;
            if (classify(stp, m_entryp, m_keyp) == Side::Key
                || classify(stp, m_entryp, m_keyp) == Side::Both || stmtBad(stp)) {
                UINFO(4, "  Wake prefix " << stp->prettyTypeName() << endl);
                return false;
            }
        }

        AstNode* const builtp = build(outerp, innerp, depth);
        if (!builtp) return false;

        AstAssign* const initp = VN_CAST(innerp->backp(), Assign);
        innerp->unlinkFrBack();
        VL_DO_DANGLING(innerp->deleteTree(), innerp);
        if (initp) {
            AstNode* const doomed = initp;
            doomed->unlinkFrBack();
            VL_DO_DANGLING(doomed->deleteTree(), doomed);
        }
        if (guardp && !guardp->thensp()) {
            AstNode* const doomed = guardp;
            doomed->unlinkFrBack();
            VL_DO_DANGLING(doomed->deleteTree(), doomed);
            guardp = nullptr;
        }
        if (!outerp->stmtsp()) {
            outerp->replaceWith(builtp);
            VL_DO_DANGLING(outerp->deleteTree(), outerp);
        } else {
            outerp->addNextHere(builtp);
        }
        ++m_nests;
        UINFO(4, "  Wake table depth=" << depth << " wb=" << nwb << " matches=" << m_matches.size()
                                       << endl);
        return true;
    }

public:
    explicit WakeVisitor(AstNetlist* nodep) {
        iterate(nodep);
        // Inners are visited after their outer. Trying them first means a
        // successful outer rewrite can delete the inner without use-after-free.
        for (size_t i = m_whiles.size(); i-- > 0;) tryOuter(m_whiles[i]);
    }
    ~WakeVisitor() override {
        V3Stats::addStat("Optimizations, Wakeup indexes inverted", m_nests);
    }
    void visit(AstWhile* nodep) override {
        m_whiles.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

}  // namespace

void V3Wake::wakeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { WakeVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("wake", 0, dumpTree() >= 6);
}
