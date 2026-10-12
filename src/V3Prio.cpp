// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lower priority encoders and lzc trees to ctz
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
// V3Prio
//
// A leading/trailing-zero count written as a balanced mux tree (the pulp
// lzc / rr_arb_tree shape) or as a counted loop with break is one host
// count-trailing-zeros. An LSB-first grant loop is one one-hot isolate.
// Both stay a handful of instructions instead of a cascade of 1-bit tests.
//
// The tree is recognized by following continuous drivers:
//
//   bit[k] ? k : k+1                         leaf, implied bit k+1
//   (|left) ? left : right                   adjacent groups
//   (|left) ? left : (left.base+left.n)      one implied high bit
//   bit[k] ? k : groupAt(k+1)                linear priority chain
//
// A full-width group with base 0 is VL_LZC_CTZ_*(vec, WIDTH-1). That value
// matches lzc on an all-zero input (cnt == WIDTH-1). The companion
// empty = ~sel_root, when sel_root ORs every bit, becomes !(|vec).
//
// Runs before the early unroll, while the loop is still a loop, and before
// V3Soa, while packed index arrays are still bit selects.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Prio.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

constexpr int kMaxWidth = 64;
constexpr int kMaxDepth = 96;

struct Loc final {
    AstVar* varp = nullptr;
    int lsb = 0;
    int width = 0;
    bool operator==(const Loc& o) const {
        return varp == o.varp && lsb == o.lsb && width == o.width;
    }
};
struct LocHash final {
    size_t operator()(const Loc& loc) const {
        return std::hash<const void*>{}(loc.varp) ^ (static_cast<size_t>(loc.lsb) << 1)
               ^ (static_cast<size_t>(loc.width) << 17);
    }
};
struct DrvEnt final {
    AstNodeExpr* exprp = nullptr;
    bool poison = false;
};
struct Bits final {
    AstVar* varp = nullptr;
    uint64_t mask = 0;
    bool ok = false;
};
struct Index final {
    bool ok = false;
    bool isConst = false;
    uint32_t constVal = 0;
    AstVar* vecp = nullptr;
    int base = 0;
    int n = 0;
};
struct UpCount final {
    AstVar* idx = nullptr;
    int trips = 0;
    AstAssign* initp = nullptr;
    AstJumpBlock* blockp = nullptr;
};
enum class Scan : uint8_t { Lsb, Msb };
using Stack = std::unordered_set<const AstNode*>;

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

bool asLoc(AstNodeExpr* nodep, Loc& loc) {
    nodep = peelCast(nodep);
    if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
        if (!refp->varp() || refp->varp()->width() <= 0) return false;
        loc = Loc{refp->varp(), 0, refp->varp()->width()};
        return true;
    }
    AstSel* const selp = VN_CAST(nodep, Sel);
    if (!selp) return false;
    AstVarRef* const refp = VN_CAST(peelCast(selp->fromp()), VarRef);
    uint32_t lsb = 0;
    uint32_t wid = 0;
    if (!refp || !refp->varp()) return false;
    if (!constUInt(selp->lsbp(), lsb) || !constUInt(selp->widthp(), wid)) return false;
    if (wid == 0 || wid > static_cast<uint32_t>(kMaxWidth) || lsb > 0x00ffffffU) return false;
    loc = Loc{refp->varp(), static_cast<int>(lsb), static_cast<int>(wid)};
    return true;
}

uint64_t rangeMask(int base, int n) {
    if (base < 0 || n <= 0 || base >= kMaxWidth || n > kMaxWidth || base + n > kMaxWidth) return 0;
    if (n == kMaxWidth) return ~0ULL;
    return ((1ULL << n) - 1ULL) << base;
}

AstVar* lhsVar(AstNodeExpr* nodep) {
    nodep = peelCast(nodep);
    if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp->varp();
    if (AstSel* const selp = VN_CAST(nodep, Sel)) {
        if (AstVarRef* const refp = VN_CAST(peelCast(selp->fromp()), VarRef)) return refp->varp();
    }
    return nullptr;
}

bool asOr(AstNodeExpr* nodep, AstNodeExpr*& ap, AstNodeExpr*& bp) {
    if (AstOr* const orp = VN_CAST(nodep, Or)) {
        ap = orp->lhsp();
        bp = orp->rhsp();
        return true;
    }
    if (AstLogOr* const orp = VN_CAST(nodep, LogOr)) {
        ap = orp->lhsp();
        bp = orp->rhsp();
        return true;
    }
    return false;
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

AstNode* unwrapBegin(AstNode* nodep) {
    if (AstBegin* const beginp = VN_CAST(nodep, Begin)) return beginp->stmtsp();
    return nodep;
}

// A call whose C++ result is resultWidth bits, then cast to the Verilog lhs.
AstNodeExpr* hostCall(FileLine* fl, const char* fname, AstVar* varp, bool withImm, uint32_t imm,
                      int resultWidth, int destWidth) {
    AstNode* const headp = new AstText{fl, std::string{fname} + "(", true};
    headp->addNext(new AstVarRef{fl, varp, VAccess::READ});
    if (withImm) {
        headp->addNext(new AstText{fl, ", ", true});
        headp->addNext(new AstConst{fl, AstConst::WidthedValue{}, 32, imm});
    }
    headp->addNext(new AstText{fl, ")", true});
    AstCExpr* const cexprp = new AstCExpr{fl, headp};
    cexprp->dtypeSetLogicSized(resultWidth, VSigning::UNSIGNED);
    cexprp->pure(true);
    cexprp->protect(false);
    if (destWidth == resultWidth) return cexprp;
    return new AstCCast{fl, cexprp, destWidth, destWidth};
}

const char* ctzName(int width) { return width <= 32 ? "VL_LZC_CTZ_I" : "VL_LZC_CTZ_Q"; }
const char* clzName(int width) { return width <= 32 ? "VL_LZC_CLZ_I" : "VL_LZC_CLZ_Q"; }
const char* onehotName(int width) { return width <= 32 ? "VL_LSBONEHOT_I" : "VL_LSBONEHOT_Q"; }
int callWidth(int width) { return width <= 32 ? 32 : 64; }

class PrioVisitor final : public VNVisitor {
    struct RhsRep final {
        AstAssignW* assignp = nullptr;
        AstNodeExpr* rhsp = nullptr;
    };

    std::unordered_map<Loc, DrvEnt, LocHash> m_drv;
    std::vector<AstAssignW*> m_assigns;
    std::vector<AstWhile*> m_whiles;
    std::vector<RhsRep> m_reps;
    VDouble0 m_lowered;

    // 0 = no continuous driver, 1 = poisoned, 2 = one driver
    int lookup(const Loc& loc, AstNodeExpr*& exprp) const {
        const auto it = m_drv.find(loc);
        if (it == m_drv.end()) return 0;
        if (it->second.poison || !it->second.exprp) return 1;
        exprp = it->second.exprp;
        return 2;
    }

    bool matchBits(AstNodeExpr* nodep, Bits& out, int depth, Stack& stack) {
        if (depth <= 0 || !nodep) return false;
        nodep = peelCast(nodep);
        if (!nodep) return false;
        if (AstConst* const cp = VN_CAST(nodep, Const)) {
            if (!cp->isZero()) return false;
            out = Bits{};
            out.ok = true;
            return true;
        }
        AstNodeExpr* ap = nullptr;
        AstNodeExpr* bp = nullptr;
        if (asOr(nodep, ap, bp)) {
            Bits lhs;
            Bits rhs;
            if (!matchBits(ap, lhs, depth - 1, stack) || !matchBits(bp, rhs, depth - 1, stack)) {
                return false;
            }
            if (lhs.varp && rhs.varp && lhs.varp != rhs.varp) return false;
            out.ok = true;
            out.varp = lhs.varp ? lhs.varp : rhs.varp;
            out.mask = lhs.mask | rhs.mask;
            return true;
        }
        if (AstRedOr* const redp = VN_CAST(nodep, RedOr)) return matchRange(redp->lhsp(), out);
        if (AstEq* const eqp = VN_CAST(nodep, Eq)) {
            if (eqp->rhsp()->isOne()) return matchBits(eqp->lhsp(), out, depth - 1, stack);
            if (eqp->lhsp()->isOne()) return matchBits(eqp->rhsp(), out, depth - 1, stack);
            return false;
        }
        if (AstNeq* const neqp = VN_CAST(nodep, Neq)) {
            if (neqp->rhsp()->isZero()) return matchBits(neqp->lhsp(), out, depth - 1, stack);
            if (neqp->lhsp()->isZero()) return matchBits(neqp->rhsp(), out, depth - 1, stack);
            return false;
        }
        Loc loc;
        if (!asLoc(nodep, loc)) return false;
        AstNodeExpr* drv = nullptr;
        const int kind = lookup(loc, drv);
        if (kind == 1) return false;
        if (kind == 2) {
            if (!stack.insert(drv).second) return false;
            const bool ok = matchBits(drv, out, depth - 1, stack);
            stack.erase(drv);
            return ok;
        }
        if (loc.width != 1 || loc.lsb < 0 || loc.lsb >= kMaxWidth) return false;
        if (loc.lsb >= loc.varp->width()) return false;
        out.ok = true;
        out.varp = loc.varp;
        out.mask = 1ULL << loc.lsb;
        return true;
    }

    bool matchRange(AstNodeExpr* nodep, Bits& out) {
        nodep = peelCast(nodep);
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (!refp->varp()) return false;
            const int width = refp->varp()->width();
            const uint64_t mask = rangeMask(0, width);
            if (!mask && width != kMaxWidth) return false;
            out.ok = true;
            out.varp = refp->varp();
            out.mask = width == kMaxWidth ? ~0ULL : mask;
            return out.mask != 0;
        }
        AstSel* const selp = VN_CAST(nodep, Sel);
        if (!selp) return false;
        AstVarRef* const refp = VN_CAST(peelCast(selp->fromp()), VarRef);
        uint32_t lsb = 0;
        uint32_t wid = 0;
        if (!refp || !refp->varp()) return false;
        if (!constUInt(selp->lsbp(), lsb) || !constUInt(selp->widthp(), wid)) return false;
        const uint64_t mask = rangeMask(static_cast<int>(lsb), static_cast<int>(wid));
        if (!mask) return false;
        out.ok = true;
        out.varp = refp->varp();
        out.mask = mask;
        return true;
    }

    bool matchIndex(AstNodeExpr* nodep, Index& out, int depth, Stack& stack) {
        if (depth <= 0 || !nodep) return false;
        nodep = peelCast(nodep);
        if (!nodep) return false;
        uint32_t cval = 0;
        if (constUInt(nodep, cval)) {
            out = Index{};
            out.ok = true;
            out.isConst = true;
            out.constVal = cval;
            return true;
        }
        if (VN_IS(nodep, VarRef) || VN_IS(nodep, Sel)) {
            Loc loc;
            AstNodeExpr* drv = nullptr;
            if (!asLoc(nodep, loc)) return false;
            if (lookup(loc, drv) != 2) return false;
            if (!stack.insert(drv).second) return false;
            const bool ok = matchIndex(drv, out, depth - 1, stack);
            stack.erase(drv);
            return ok;
        }
        AstCond* const condp = VN_CAST(nodep, Cond);
        if (!condp) return false;
        Index thenI;
        Index elseI;
        if (!matchIndex(condp->thenp(), thenI, depth - 1, stack)) return false;
        if (!matchIndex(condp->elsep(), elseI, depth - 1, stack)) return false;

        // bit[k] ? k : k+1. The high bit is implied: both "only that bit" and
        // "neither bit" yield k+1, which is the lzc empty value for the pair.
        if (thenI.isConst && elseI.isConst && elseI.constVal == thenI.constVal + 1
            && thenI.constVal < static_cast<uint32_t>(kMaxWidth)) {
            Bits bits;
            if (!matchBits(condp->condp(), bits, depth - 1, stack) || !bits.varp) return false;
            if (bits.mask != (1ULL << thenI.constVal)) return false;
            out = Index{};
            out.ok = true;
            out.vecp = bits.varp;
            out.base = static_cast<int>(thenI.constVal);
            out.n = 2;
            return out.base + out.n <= bits.varp->width();
        }
        if (!thenI.isConst && !elseI.isConst && thenI.vecp && thenI.vecp == elseI.vecp
            && elseI.base == thenI.base + thenI.n) {
            Bits bits;
            const uint64_t need = rangeMask(thenI.base, thenI.n);
            if (!need || !matchBits(condp->condp(), bits, depth - 1, stack)) return false;
            if (bits.varp != thenI.vecp || bits.mask != need) return false;
            out = thenI;
            out.n = thenI.n + elseI.n;
            return out.base + out.n <= thenI.vecp->width();
        }
        if (!thenI.isConst && elseI.isConst
            && elseI.constVal == static_cast<uint32_t>(thenI.base + thenI.n)) {
            Bits bits;
            const uint64_t need = rangeMask(thenI.base, thenI.n);
            if (!need || !matchBits(condp->condp(), bits, depth - 1, stack)) return false;
            if (bits.varp != thenI.vecp || bits.mask != need) return false;
            out = thenI;
            out.n = thenI.n + 1;
            return out.base + out.n <= thenI.vecp->width();
        }
        if (thenI.isConst && !elseI.isConst && elseI.vecp
            && elseI.base == static_cast<int>(thenI.constVal) + 1
            && thenI.constVal < static_cast<uint32_t>(kMaxWidth)) {
            Bits bits;
            if (!matchBits(condp->condp(), bits, depth - 1, stack)) return false;
            if (bits.varp != elseI.vecp || bits.mask != (1ULL << thenI.constVal)) return false;
            out = elseI;
            out.base = static_cast<int>(thenI.constVal);
            out.n = elseI.n + 1;
            return out.base + out.n <= elseI.vecp->width();
        }
        return false;
    }

    bool fullCover(AstNodeExpr* nodep, AstVar*& vecp) {
        Bits bits;
        Stack stack;
        if (!matchBits(nodep, bits, kMaxDepth, stack) || !bits.varp) return false;
        const int width = bits.varp->width();
        if (width < 1 || width > kMaxWidth) return false;
        const uint64_t all = width == kMaxWidth ? ~0ULL : rangeMask(0, width);
        if (!all || bits.mask != all) return false;
        vecp = bits.varp;
        return true;
    }

    AstNodeExpr* makeCount(FileLine* fl, bool lsb, AstVar* vecp, int destWidth) {
        const int width = vecp->width();
        const char* const name = lsb ? ctzName(width) : clzName(width);
        const uint32_t imm = lsb ? static_cast<uint32_t>(width - 1) : static_cast<uint32_t>(width);
        // CTZ/CLZ results fit in 32 bits. The Q form only widens the input.
        return hostCall(fl, name, vecp, true, imm, 32, destWidth);
    }

    // Record the new RHS. Drivers are still the original nodes until lower()
    // applies every replacement, so one root can be followed by another.
    bool tryEmpty(AstAssignW* nodep) {
        AstNodeExpr* rhs = peelCast(nodep->rhsp());
        if (AstNot* const notp = VN_CAST(rhs, Not)) {
            rhs = notp->lhsp();
        } else if (AstLogNot* const notp = VN_CAST(rhs, LogNot)) {
            rhs = notp->lhsp();
        } else {
            return false;
        }
        if (VN_IS(peelCast(rhs), RedOr)) return false;  // already !(|vec) or ~(|vec)
        if (nodep->lhsp()->width() != 1) return false;
        AstVar* vecp = nullptr;
        if (!fullCover(rhs, vecp)) return false;
        if (lhsVar(nodep->lhsp()) == vecp) return false;
        FileLine* const fl = nodep->fileline();
        m_reps.push_back(
            {nodep, new AstLogNot{fl, new AstRedOr{fl, new AstVarRef{fl, vecp, VAccess::READ}}}});
        UINFO(4, "  Prio empty " << vecp->prettyNameQ() << endl);
        return true;
    }

    bool tryTree(AstAssignW* nodep) {
        Index idx;
        Stack stack;
        if (!matchIndex(nodep->rhsp(), idx, kMaxDepth, stack)) return false;
        if (idx.isConst || !idx.vecp || idx.base != 0) return false;
        const int width = idx.vecp->width();
        if (idx.n != width || width < 2 || width > kMaxWidth) return false;
        if (lhsVar(nodep->lhsp()) == idx.vecp) return false;
        const int dest = nodep->lhsp()->width();
        if (dest < 1) return false;
        m_reps.push_back({nodep, makeCount(nodep->fileline(), true, idx.vecp, dest)});
        UINFO(4, "  Prio ctz " << idx.vecp->prettyNameQ() << " w" << width << endl);
        return true;
    }

    bool matchUpCount(AstWhile* nodep, UpCount& out) {
        AstNode* place = nodep;
        if (AstJumpBlock* const blockp = VN_CAST(nodep->backp(), JumpBlock)) {
            if (blockp->stmtsp() != nodep) return false;
            place = blockp;
            out.blockp = blockp;
        }
        AstAssign* const initp = VN_CAST(place->backp(), Assign);
        if (!initp) return false;
        AstVar* const idx = peelVar(initp->lhsp());
        uint32_t initVal = 0;
        if (!idx || !constUInt(initp->rhsp(), initVal) || initVal != 0) return false;
        AstAssign* const incp = VN_CAST(nodep->incsp(), Assign);
        if (!incp || incp->nextp()) return false;
        if (peelVar(incp->lhsp()) != idx) return false;
        AstAdd* const addp = VN_CAST(peelCast(incp->rhsp()), Add);
        if (!addp) return false;
        AstNodeExpr* stepExpr = nullptr;
        if (peelVar(addp->lhsp()) == idx) {
            stepExpr = addp->rhsp();
        } else if (peelVar(addp->rhsp()) == idx) {
            stepExpr = addp->lhsp();
        } else {
            return false;
        }
        uint32_t step = 0;
        if (!constUInt(stepExpr, step) || step != 1) return false;

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
        if (peelVar(varSide) != idx) return false;
        uint32_t bound = 0;
        if (!constUInt(boundSide, bound) || bound < 1 || bound > static_cast<uint32_t>(kMaxWidth)) {
            return false;
        }
        out.idx = idx;
        out.trips = static_cast<int>(bound);
        out.initp = initp;
        return true;
    }

    // req[i], or req[(W-1)-i]. The index may be truncated to the address width.
    bool bitScan(AstNodeExpr* expr, AstVar* idx, AstVar*& vecp, Scan& scan) {
        expr = peelCast(expr);
        if (AstEq* const eqp = VN_CAST(expr, Eq)) {
            if (eqp->rhsp()->isOne()) return bitScan(eqp->lhsp(), idx, vecp, scan);
            if (eqp->lhsp()->isOne()) return bitScan(eqp->rhsp(), idx, vecp, scan);
            return false;
        }
        if (AstNeq* const neqp = VN_CAST(expr, Neq)) {
            if (neqp->rhsp()->isZero()) return bitScan(neqp->lhsp(), idx, vecp, scan);
            if (neqp->lhsp()->isZero()) return bitScan(neqp->rhsp(), idx, vecp, scan);
            return false;
        }
        AstSel* const selp = VN_CAST(expr, Sel);
        if (!selp) return false;
        uint32_t wid = 0;
        if (!constUInt(selp->widthp(), wid) || wid != 1) return false;
        AstVarRef* const refp = VN_CAST(peelCast(selp->fromp()), VarRef);
        if (!refp || !refp->varp()) return false;
        vecp = refp->varp();
        AstNodeExpr* const lsb = peelCast(selp->lsbp());
        if (peelVar(lsb) == idx) {
            scan = Scan::Lsb;
            return true;
        }
        if (AstSub* const subp = VN_CAST(lsb, Sub)) {
            uint32_t cval = 0;
            if (constUInt(subp->lhsp(), cval) && peelVar(subp->rhsp()) == idx
                && cval + 1 == static_cast<uint32_t>(vecp->width())) {
                scan = Scan::Msb;
                return true;
            }
        }
        return false;
    }

    bool tryFind(AstWhile* nodep) {
        UpCount up;
        if (!matchUpCount(nodep, up) || !up.blockp) return false;
        AstNode* const body = unwrapBegin(nodep->stmtsp());
        if (!body || body->nextp()) return false;
        AstIf* const ifp = VN_CAST(body, If);
        if (!ifp || ifp->elsesp()) return false;
        AstNode* then = unwrapBegin(ifp->thensp());
        AstAssign* asgp = nullptr;
        AstJumpGo* jumpp = nullptr;
        int nstmt = 0;
        for (AstNode* stp = then; stp; stp = stp->nextp()) {
            ++nstmt;
            if (AstAssign* const ap = VN_CAST(stp, Assign)) {
                asgp = ap;
            } else if (AstJumpGo* const jp = VN_CAST(stp, JumpGo)) {
                jumpp = jp;
            } else {
                return false;
            }
        }
        if (nstmt != 2 || !asgp || !jumpp) return false;
        if (jumpp->labelp() != up.blockp->labelp()) return false;
        AstVar* vecp = nullptr;
        Scan scan = Scan::Lsb;
        if (!bitScan(ifp->condp(), up.idx, vecp, scan)) return false;
        if (!vecp || vecp->width() != up.trips || up.trips < 1 || up.trips > kMaxWidth) return false;
        if (peelVar(asgp->rhsp()) != up.idx) return false;
        if (!VN_IS(peelCast(asgp->lhsp()), VarRef)) return false;
        const int dest = asgp->lhsp()->width();
        if (dest < 1) return false;
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const countp = makeCount(fl, scan == Scan::Lsb, vecp, dest);
        AstAssign* const newp = new AstAssign{fl, asgp->lhsp()->cloneTree(false), countp};
        // The loop writes idx only when some bit is set, so a pre-loop default
        // survives an all-zero vector. VL_LZC_* is defined on zero either way.
        AstIf* const guardp = new AstIf{fl, new AstRedOr{fl, new AstVarRef{fl, vecp, VAccess::READ}}, newp};
        nodep->replaceWith(guardp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        ++m_lowered;
        UINFO(4, "  Prio find " << (scan == Scan::Lsb ? "ctz " : "clz ") << vecp->prettyNameQ()
                                << endl);
        return true;
    }

    bool notFound(AstNodeExpr* nodep, AstVar*& foundp) {
        nodep = peelCast(nodep);
        AstNodeExpr* inner = nullptr;
        if (AstNot* const notp = VN_CAST(nodep, Not)) {
            inner = notp->lhsp();
        } else if (AstLogNot* const notp = VN_CAST(nodep, LogNot)) {
            inner = notp->lhsp();
        } else {
            return false;
        }
        foundp = peelVar(inner);
        return foundp && foundp->width() == 1;
    }

    bool tryGrant(AstWhile* nodep) {
        UpCount up;
        if (!matchUpCount(nodep, up) || up.blockp) return false;
        AstNode* const body = unwrapBegin(nodep->stmtsp());
        if (!body) return false;
        AstAssign* const gntAsg = VN_CAST(body, Assign);
        AstAssign* const foundAsg = body->nextp() ? VN_CAST(body->nextp(), Assign) : nullptr;
        if (!gntAsg || !foundAsg || foundAsg->nextp()) return false;

        AstVar* gnt = nullptr;
        Scan gscan = Scan::Lsb;
        if (!bitScan(gntAsg->lhsp(), up.idx, gnt, gscan) || gscan != Scan::Lsb || !gnt) return false;

        AstNodeExpr* ap = nullptr;
        AstNodeExpr* bp = nullptr;
        if (!asAnd(peelCast(gntAsg->rhsp()), ap, bp)) return false;
        AstVar* req = nullptr;
        AstVar* found = nullptr;
        Scan rscan = Scan::Lsb;
        auto split = [&](AstNodeExpr* bitp, AstNodeExpr* notp) -> bool {
            AstVar* got = nullptr;
            if (!bitScan(bitp, up.idx, got, rscan) || rscan != Scan::Lsb) return false;
            req = got;
            return notFound(notp, found);
        };
        if (!split(ap, bp) && !split(bp, ap)) return false;
        if (!req || req == gnt || req->width() != gnt->width() || gnt->width() != up.trips) {
            return false;
        }

        if (peelVar(foundAsg->lhsp()) != found) return false;
        AstNodeExpr* op = nullptr;
        AstNodeExpr* oq = nullptr;
        if (!asOr(peelCast(foundAsg->rhsp()), op, oq)) return false;
        AstVar* orReq = nullptr;
        Scan oscan = Scan::Lsb;
        auto orSplit = [&](AstNodeExpr* varp, AstNodeExpr* bitp) -> bool {
            if (peelVar(varp) != found) return false;
            AstVar* got = nullptr;
            return bitScan(bitp, up.idx, got, oscan) && oscan == Scan::Lsb && got == req;
        };
        if (!orSplit(op, oq) && !orSplit(oq, op)) return false;

        AstAssign* const foundInit = VN_CAST(up.initp->backp(), Assign);
        if (!foundInit || peelVar(foundInit->lhsp()) != found || !foundInit->rhsp()->isZero()) {
            return false;
        }

        FileLine* const fl = nodep->fileline();
        const int width = req->width();
        AstNodeExpr* const hotp = hostCall(fl, onehotName(width), req, false, 0, callWidth(width),
                                           gnt->width());
        AstAssign* const hotAsg
            = new AstAssign{fl, new AstVarRef{fl, gnt, VAccess::WRITE}, hotp};
        AstAssign* const redAsg = new AstAssign{
            fl, new AstVarRef{fl, found, VAccess::WRITE},
            new AstRedOr{fl, new AstVarRef{fl, req, VAccess::READ}}};
        hotAsg->addNext(redAsg);
        nodep->replaceWith(hotAsg);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        ++m_lowered;
        UINFO(4, "  Prio grant " << req->prettyNameQ() << " w" << width << endl);
        return true;
    }

    void lower() {
        for (AstAssignW* const assignp : m_assigns) {
            if (tryEmpty(assignp)) continue;
            tryTree(assignp);
        }
        for (const RhsRep& rep : m_reps) {
            AstNodeExpr* const oldp = rep.assignp->rhsp();
            oldp->replaceWith(rep.rhsp);
            VL_DO_DANGLING(oldp->deleteTree(), oldp);
            ++m_lowered;
        }
        for (AstWhile* const whilep : m_whiles) {
            if (tryFind(whilep)) continue;
            tryGrant(whilep);
        }
    }

public:
    explicit PrioVisitor(AstNetlist* nodep) {
        iterate(nodep);
        lower();
    }
    ~PrioVisitor() override {
        V3Stats::addStat("Optimizations, Priority encoders lowered", m_lowered);
    }
    void visit(AstAssignW* nodep) override {
        Loc loc;
        if (asLoc(nodep->lhsp(), loc)) {
            const auto it = m_drv.find(loc);
            if (it == m_drv.end()) {
                m_drv.emplace(loc, DrvEnt{nodep->rhsp(), false});
            } else {
                it->second.exprp = nullptr;
                it->second.poison = true;
            }
        }
        m_assigns.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstWhile* nodep) override {
        m_whiles.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

}  // namespace

void V3Prio::prioAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { PrioVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("prio", 0, dumpTree() >= 6);
}
