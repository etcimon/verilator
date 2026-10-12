// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Set dirty bits on stores to hybrid cut signals
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
// V3Dirty
//
// SenExprBuilder samples a wide hybrid cut as "a dirty bit is set, and the
// value after the last pass differs." A store only sets bits:
//
//   * whole variable, or a dynamic index: dirty_all (one bit, every slice
//     may wake)
//   * constant part select: one bit per 32-bit word the select covers
//
// The compare stays in the trigger function and runs only when a bit is
// set, so a pass that stores and then restores the same value converges.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Dirty.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

AstNodeStmt* setBit(FileLine* flp, AstVarScope* wordsp, int bit) {
    AstSel* const selp = new AstSel{flp, new AstVarRef{flp, wordsp, VAccess::WRITE}, bit, 1};
    return new AstAssign{flp, selp, new AstConst{flp, AstConst::BitTrue{}}};
}

AstNodeStmt* setAll(FileLine* flp, AstVarScope* allp) {
    return new AstAssign{flp, new AstVarRef{flp, allp, VAccess::WRITE},
                         new AstConst{flp, AstConst::BitTrue{}}};
}

// Constant part-select of this variable, or a whole-variable reference.
// Anything else (dynamic index, concat, a mix of variables) is a dirty_all
// store: correct, and still one bit.
bool constRange(AstNodeExpr* lhsp, AstVarScope* vscp, int& lsb, int& width) {
    if (AstVarRef* const refp = VN_CAST(lhsp, VarRef)) {
        if (refp->varScopep() != vscp) return false;
        lsb = 0;
        width = vscp->width();
        return true;
    }
    AstSel* const selp = VN_CAST(lhsp, Sel);
    if (!selp) return false;
    AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef);
    if (!refp || refp->varScopep() != vscp) return false;
    if (!VN_IS(selp->lsbp(), Const) || !VN_IS(selp->widthp(), Const)) return false;
    lsb = selp->lsbConst();
    width = selp->widthConst();
    return width > 0;
}

void instrument(AstNodeAssign* assignp) {
    std::vector<AstVarScope*> tracked;
    assignp->lhsp()->foreach([&](AstVarRef* refp) {
        if (!refp->access().isWriteOrRW()) return;
        AstVarScope* const vscp = refp->varScopep();
        if (!vscp || !vscp->dirtyWordsp()) return;
        for (AstVarScope* const have : tracked) {
            if (have == vscp) return;
        }
        tracked.push_back(vscp);
    });
    if (tracked.empty()) return;

    FileLine* const flp = assignp->fileline();
    AstNode* listp = nullptr;
    const auto add = [&](AstNodeStmt* stmtp) { listp = AstNode::addNext(listp, stmtp); };
    if (tracked.size() != 1) {
        for (AstVarScope* const vscp : tracked) add(setAll(flp, vscp->dirtyAllp()));
    } else {
        AstVarScope* const vscp = tracked.front();
        int lsb = 0;
        int width = 0;
        if (!constRange(assignp->lhsp(), vscp, lsb, width) || width >= vscp->width()) {
            add(setAll(flp, vscp->dirtyAllp()));
        } else {
            const int nWords = vscp->dirtyWordsp()->width();
            int w0 = lsb >> 5;
            int w1 = (lsb + width - 1) >> 5;
            if (w0 < 0) w0 = 0;
            if (w1 >= nWords) w1 = nWords - 1;
            for (int bit = w0; bit <= w1; ++bit) add(setBit(flp, vscp->dirtyWordsp(), bit));
            if (!listp) add(setAll(flp, vscp->dirtyAllp()));
        }
    }
    assignp->addHereThisAsNext(listp);
    V3Stats::addStat("Optimizations, Dirty-bit stores", 1);
}

}  // namespace

void V3Dirty::dirtyAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    std::vector<AstNodeAssign*> assigns;
    nodep->foreach([&](AstNodeAssign* assignp) { assigns.push_back(assignp); });
    for (AstNodeAssign* const assignp : assigns) instrument(assignp);
}
