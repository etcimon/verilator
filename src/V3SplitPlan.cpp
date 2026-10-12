// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Mark combinational-cycle variables for splitting
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
// V3SplitPlan
//
// V3SplitVar only splits a variable that already carries split_var, and it
// runs before scope and scheduling. The UNOPTFLAT report inside breakCycles
// is therefore too late to drive it. This pass builds the same kind of
// bipartite statement/variable graph the scheduler will see once each
// combinational assignment is its own block, and marks the internal
// variables that sit in a cycle.
//
// Every splittable variable in the cycle is marked, including ones the
// splitter will later refuse (a dynamic index, a public signal it cannot
// prove). Those marks are not removed and the pass does not run again.
// V3SplitVar is not monotone: dropping a refused variable and retrying
// unsplits neighbors whose access boundaries moved with it. A refused
// variable stays whole and, when it is a wide hybrid cut, is change-detected
// with dirty bits instead.
//
// Ports are left whole. A port that is read or written as one vector is a
// dirty-bit residual, not a split. The splitter's own plan (constant bit
// ranges, and a mux for a small dynamic element read) is unchanged.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3SplitPlan.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

class PlanGraph final : public V3Graph {};

class StmtVertex final : public V3GraphVertex {
public:
    explicit StmtVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    string name() const override { return "stmt"; }  // LCOV_EXCL_LINE
};

class PlanVarVertex final : public V3GraphVertex {
    AstVar* const m_varp;

public:
    PlanVarVertex(V3Graph* graphp, AstVar* varp)
        : V3GraphVertex{graphp}
        , m_varp{varp} {}
    AstVar* varp() const { return m_varp; }
    string name() const override { return m_varp->name(); }  // LCOV_EXCL_LINE
};

// True when this assignment is combinational. A clocked block is not a
// candidate: the scheduler does not put it in the combinational graph.
// Tasks are still uninlined here, so a cycle that only exists inside a
// task is left for a later dirty-bit cut.
bool inCombo(AstNode* nodep) {
    for (AstNode* backp = nodep; backp; backp = backp->backp()) {
        if (VN_IS(backp, NodeFTask)) return false;
        if (VN_IS(backp, Initial) || VN_IS(backp, Final)) return false;
        if (AstAlways* const alwp = VN_CAST(backp, Always)) {
            const VAlwaysKwd kwd = alwp->keyword();
            if (kwd == VAlwaysKwd::ALWAYS_FF) return false;
            if (kwd == VAlwaysKwd::ALWAYS_COMB || kwd == VAlwaysKwd::ALWAYS_LATCH) return true;
            const AstSenTree* const senp = alwp->sensesp();
            if (!senp || !senp->sensesp()) return true;
            // An edge in the sensitivity list is a clocked process. Combo
            // cycles are the ones split_var can turn back into acyclic bits.
            if (senp->hasClocked()) return false;
            return true;
        }
    }
    return VN_IS(nodep, AssignW) || VN_IS(nodep, AssignAlias);
}

}  // namespace

void V3SplitPlan::splitPlanAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    std::vector<AstNodeAssign*> assigns;
    nodep->foreach([&](AstNodeAssign* assignp) {
        if (inCombo(assignp)) assigns.push_back(assignp);
    });
    if (assigns.empty()) return;

    PlanGraph graph;
    std::unordered_map<AstVar*, PlanVarVertex*> varVtx;
    const auto vtxOf = [&](AstVar* varp) {
        const auto it = varVtx.find(varp);
        if (it != varVtx.end()) return it->second;
        PlanVarVertex* const vtxp = new PlanVarVertex{&graph, varp};
        varVtx.emplace(varp, vtxp);
        return vtxp;
    };

    for (AstNodeAssign* const assignp : assigns) {
        std::unordered_set<AstVar*> reads;
        std::unordered_set<AstVar*> writes;
        assignp->foreach([&](AstVarRef* refp) {
            AstVar* const varp = refp->varp();
            if (!varp) return;
            if (refp->access().isReadOrRW()) reads.insert(varp);
            if (refp->access().isWriteOrRW()) writes.insert(varp);
        });
        if (reads.empty() && writes.empty()) continue;
        StmtVertex* const stmtp = new StmtVertex{&graph};
        // A read and a write of the same variable in one assignment is a
        // self-cycle at variable granularity. That is the false UNOPTFLAT
        // split_var exists to remove, so both directions are kept.
        for (AstVar* const varp : reads) {
            new V3GraphEdge{&graph, vtxOf(varp), stmtp, 1, true};
        }
        for (AstVar* const varp : writes) {
            new V3GraphEdge{&graph, stmtp, vtxOf(varp), 1, true};
        }
    }

    graph.stronglyConnected(&V3GraphEdge::followAlwaysTrue);

    int marked = 0;
    for (const auto& pair : varVtx) {
        AstVar* const varp = pair.first;
        if (pair.second->color() == 0) continue;  // Not in a multi-node cycle
        if (varp->attrSplitVar()) continue;  // User mark, or already recorded
        if (varp->isIO()) continue;  // Ports used whole stay for dirty bits
        if (!V3SplitVar::canSplitVar(varp)) continue;
        varp->attrSplitVar(true);
        varp->attrSplitAuto(true);
        ++marked;
        UINFO(4, "SplitPlan " << varp->prettyNameQ() << " width " << varp->width() << endl);
    }
    V3Stats::addStat("SplitVar, auto split variables", marked);
}
