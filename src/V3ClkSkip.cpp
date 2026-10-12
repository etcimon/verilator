// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Skip stable per-instance combinational code
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
// V3ClkSkip
//
// A gated core's always_ff already sits under its clock trigger. Its
// combinational copy does not: after inlining, every instance's input
// combo shares one function that the input region calls on every
// evaluation. Each inlined instance is guarded with a value compare of the
// nets that combo actually reads. A hash is not used; a collision would
// skip a real change. A free-running clock does not by itself keep the
// instance live unless that combo reads the clock.
//
// Clocked NBA functions are not guarded. They already run only on the
// edge, and a counter on that edge is not a pure function of its inputs.
// NBA MTasks are unchanged. The combo this skips is the serial input
// region, which is the part a clock gate does not remove.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3ClkSkip.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

constexpr int kMaxInputs = 64;
constexpr int kMaxBits = 4096;

bool guardFuncName(const string& name) {
    if (name.rfind("_ico_", 0) == 0) return true;
    if (name.rfind("_stl_", 0) == 0) return true;
    // Multi-domain combo keeps the _comb tag in the active and NBA regions.
    // A single-clock sequent function also holds the edge update, so it stays.
    return name.find("_comb__") != string::npos;
}

bool impureNode(const AstNode* nodep) {
    return VN_IS(nodep, CCall) || VN_IS(nodep, CMethodHard) || VN_IS(nodep, CMethodCall)
           || VN_IS(nodep, CNew) || VN_IS(nodep, UCFunc) || VN_IS(nodep, FuncRef)
           || VN_IS(nodep, TaskRef) || VN_IS(nodep, VarXRef) || VN_IS(nodep, Display)
           || VN_IS(nodep, Finish) || VN_IS(nodep, Stop) || VN_IS(nodep, MonitorOff)
           || VN_IS(nodep, FOpen) || VN_IS(nodep, FClose) || VN_IS(nodep, ReadMem)
           || VN_IS(nodep, WriteMem) || VN_IS(nodep, Rand) || VN_IS(nodep, CStmt)
           || VN_IS(nodep, AssignDly) || VN_IS(nodep, SysFuncAsTask) || VN_IS(nodep, Time)
           || VN_IS(nodep, Assert) || VN_IS(nodep, CoverInc) || VN_IS(nodep, CoverToggle)
           || VN_IS(nodep, FireEvent);
}

// AstNeq is only emitted for packed integral values. Anything else is left
// unguarded rather than compared incorrectly.
bool comparableInput(const AstVarScope* vscp) {
    if (!vscp->dtypep()) return false;
    const AstNodeDType* const dtp = vscp->dtypep()->skipRefp();
    if (!dtp || !dtp->isIntegralOrPacked()) return false;
    if (vscp->varp()->isDouble() || vscp->varp()->isString()) return false;
    return vscp->width() > 0;
}

// Inlined names still carry the cell: "t__DOT__u0__DOT__q". The instance is
// the path without the final component. Internal temps (__V...) are not
// instances, and a bare top-module net ("t__DOT__side") is not one either.
string instanceOfName(const string& name) {
    if (name.rfind("__V", 0) == 0) return {};
    const string::size_type pos = name.rfind("__DOT__");
    if (pos == string::npos || pos == 0) return {};
    return name.substr(0, pos);
}

// Parent nets and the cell share a combo statement. It belongs to the
// deepest cell when every other id is a path prefix of that cell. Sibling
// cells in one statement stay shared. The top module id has no dot.
string statementInstance(const std::unordered_set<string>& ids) {
    string best;
    for (const string& id : ids) {
        if (id.size() > best.size()) best = id;
    }
    if (best.empty() || best.find("__DOT__") == string::npos) return {};
    for (const string& id : ids) {
        if (id == best) continue;
        if (best.rfind(id + "__DOT__", 0) != 0) return {};
    }
    return best;
}

AstCFunc* enclosingFunc(AstNode* nodep) {
    AstNode* bp = nodep;
    while (bp) {
        if (AstCFunc* const funcp = VN_CAST(bp, CFunc)) return funcp;
        while (bp->backp() && bp->backp()->nextp() == bp) bp = bp->backp();
        bp = bp->backp();
    }
    return nullptr;
}

void addList(AstNode*& headp, AstNode* nodep) {
    if (!nodep) return;
    if (!headp) headp = nodep;
    else headp->addNext(nodep);
}

struct InstGroup final {
    std::vector<AstNode*> m_stmts;
    std::vector<AstVarScope*> m_reads;
    std::unordered_set<AstVarScope*> m_readSet;
    std::unordered_set<AstVarScope*> m_writes;
    bool m_refuse = false;
    string m_why;
    void noteRead(AstVarScope* vscp) {
        if (m_readSet.insert(vscp).second) m_reads.push_back(vscp);
    }
};

AstNodeExpr* differCond(FileLine* flp, AstVarScope* initedp, const std::vector<AstVarScope*>& inputs,
                        const std::vector<AstVarScope*>& shadows) {
    AstNodeExpr* condp = new AstLogNot{flp, new AstVarRef{flp, initedp, VAccess::READ}};
    for (size_t i = 0; i < inputs.size(); ++i) {
        AstNodeExpr* const neqp = new AstNeq{flp, new AstVarRef{flp, inputs[i], VAccess::READ},
                                             new AstVarRef{flp, shadows[i], VAccess::READ}};
        condp = new AstLogOr{flp, condp, neqp};
    }
    return condp;
}

AstNode* sampleBody(FileLine* flp, AstVarScope* initedp, const std::vector<AstVarScope*>& inputs,
                    const std::vector<AstVarScope*>& shadows) {
    AstNode* bodyp = new AstAssign{flp, new AstVarRef{flp, initedp, VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitTrue{}}};
    for (size_t i = 0; i < inputs.size(); ++i) {
        bodyp->addNext(new AstAssign{flp, new AstVarRef{flp, shadows[i], VAccess::WRITE},
                                     new AstVarRef{flp, inputs[i], VAccess::READ}});
    }
    return bodyp;
}

}  // namespace

void V3ClkSkip::clkSkipAll(AstNetlist* netlistp) {
    UINFO(4, __FUNCTION__ << ": " << endl);

    std::vector<AstCFunc*> funcs;
    std::unordered_map<const AstCFunc*, std::vector<AstCCall*>> callsOf;
    netlistp->foreach([&](AstCFunc* funcp) { funcs.push_back(funcp); });
    netlistp->foreach([&](AstCCall* callp) {
        if (callp->funcp()) callsOf[callp->funcp()].push_back(callp);
    });

    std::unordered_set<string> counted;
    int seq = 0;

    for (AstCFunc* const funcp : funcs) {
        if (!funcp->scopep() || !funcp->stmtsp() || !guardFuncName(funcp->name())) continue;
        // Inlined logic lives in the top scope, mixed across instances.
        // A non-top function is already one instance; its call is guarded.
        const bool splitInstances = funcp->scopep()->isTop();

        std::vector<AstNode*> stmts;
        for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) stmts.push_back(stmtp);

        std::vector<string> order;
        std::unordered_map<string, InstGroup> groups;
        std::unordered_set<AstVarScope*> otherWrites;
        const auto groupOf = [&](const string& id) -> InstGroup& {
            const auto inserted = groups.emplace(id, InstGroup{});
            if (inserted.second) order.push_back(id);
            return inserted.first->second;
        };

        for (AstNode* const stmtp : stmts) {
            bool impure = false;
            stmtp->foreach([&](const AstNode* nodep) {
                if (impureNode(nodep)) impure = true;
            });
            std::vector<AstVarRef*> refs;
            stmtp->foreach([&](AstVarRef* refp) { refs.push_back(refp); });

            std::unordered_set<string> ids;
            bool unscoped = false;
            for (const AstVarRef* const refp : refs) {
                if (!refp->varScopep()) {
                    unscoped = true;
                    continue;
                }
                if (!splitInstances) continue;
                const string id = instanceOfName(refp->varp()->name());
                if (!id.empty()) ids.insert(id);
            }

            if (!splitInstances) {
                InstGroup& inst = groupOf(funcp->scopep()->name());
                if (impure || unscoped) {
                    inst.m_refuse = true;
                    inst.m_why = impure ? "impure combo" : "unscoped reference";
                }
                for (AstVarRef* const refp : refs) {
                    if (!refp->varScopep()) continue;
                    AstVarScope* const vscp = refp->varScopep();
                    if (refp->access().isWriteOrRW()) inst.m_writes.insert(vscp);
                    if (refp->access().isReadOrRW()) inst.noteRead(vscp);
                }
                continue;
            }

            const string id = statementInstance(ids);
            if (impure || unscoped || id.empty()) {
                for (const AstVarRef* const refp : refs) {
                    if (refp->varScopep() && refp->access().isWriteOrRW()) {
                        otherWrites.insert(refp->varScopep());
                    }
                }
                if (impure || unscoped) {
                    for (const string& one : ids) {
                        if (one.find("__DOT__") == string::npos) continue;
                        InstGroup& inst = groupOf(one);
                        inst.m_refuse = true;
                        inst.m_why = impure ? "impure combo" : "unscoped reference";
                    }
                }
                continue;
            }

            InstGroup& inst = groupOf(id);
            inst.m_stmts.push_back(stmtp);
            for (AstVarRef* const refp : refs) {
                AstVarScope* const vscp = refp->varScopep();
                if (refp->access().isWriteOrRW()) inst.m_writes.insert(vscp);
                if (refp->access().isReadOrRW()) inst.noteRead(vscp);
            }
        }

        struct Ready final {
            string m_id;
            std::vector<AstNode*> m_stmts;
            std::vector<AstVarScope*> m_inputs;
        };
        std::vector<Ready> ready;
        for (const string& id : order) {
            InstGroup& inst = groups[id];
            if (splitInstances && inst.m_stmts.empty()) continue;
            if (inst.m_refuse) {
                UINFO(4, "ClkSkip refuse " << id << ": " << inst.m_why << endl);
                continue;
            }
            Ready item;
            item.m_id = id;
            item.m_stmts = inst.m_stmts;
            int bits = 0;
            bool refuse = false;
            for (AstVarScope* const vscp : inst.m_reads) {
                if (otherWrites.count(vscp)) {
                    refuse = true;
                    UINFO(4, "ClkSkip refuse " << id << ": input written outside" << endl);
                    break;
                }
                if (inst.m_writes.count(vscp)) continue;
                if (vscp->varp()->isParam()) continue;
                if (!comparableInput(vscp)) {
                    refuse = true;
                    UINFO(4, "ClkSkip refuse " << id << ": non-integral input" << endl);
                    break;
                }
                item.m_inputs.push_back(vscp);
                bits += vscp->width();
                if (item.m_inputs.size() > kMaxInputs || bits > kMaxBits) {
                    refuse = true;
                    UINFO(4, "ClkSkip refuse " << id << ": compare too wide" << endl);
                    break;
                }
            }
            if (refuse) continue;
            ready.push_back(std::move(item));
        }
        if (ready.empty()) continue;

        FileLine* const flp = funcp->fileline();
        AstScope* const scopep = funcp->scopep();

        if (!splitInstances) {
            // One function, one instance. Gate the call, not each statement,
            // so every statement still runs when the instance is live.
            const auto found = callsOf.find(funcp);
            if (found == callsOf.end()) continue;
            std::vector<AstStmtExpr*> sites;
            for (AstCCall* const callp : found->second) {
                AstStmtExpr* const stmtp = VN_CAST(callp->backp(), StmtExpr);
                if (!stmtp || stmtp->exprp() != callp) continue;
                if (enclosingFunc(stmtp) == funcp) continue;
                sites.push_back(stmtp);
            }
            if (sites.empty()) continue;
            const int idNum = seq++;
            AstVarScope* const initedp = scopep->createTemp("__Vclkskip" + cvtToStr(idNum) + "_i", 1);
            std::vector<AstVarScope*> shadows;
            for (size_t i = 0; i < ready[0].m_inputs.size(); ++i) {
                shadows.push_back(scopep->createTempLike(
                    "__Vclkskip" + cvtToStr(idNum) + "_s" + cvtToStr(i), ready[0].m_inputs[i]));
            }
            bool wrapped = false;
            for (AstStmtExpr* const stmtp : sites) {
                AstNodeExpr* const condp = differCond(flp, initedp, ready[0].m_inputs, shadows);
                AstIf* const ifp = new AstIf{stmtp->fileline(), condp};
                ifp->addThensp(sampleBody(flp, initedp, ready[0].m_inputs, shadows));
                stmtp->replaceWith(ifp);
                ifp->addThensp(stmtp);
                wrapped = true;
            }
            if (wrapped) {
                counted.insert(ready[0].m_id);
                UINFO(4, "ClkSkip guard scope " << ready[0].m_id
                                                << " inputs=" << ready[0].m_inputs.size() << endl);
            }
            continue;
        }

        AstNode* prologp = nullptr;
        for (const Ready& item : ready) {
            const int idNum = seq++;
            AstVarScope* const initedp = scopep->createTemp("__Vclkskip" + cvtToStr(idNum) + "_i", 1);
            AstVarScope* const runp = scopep->createTemp("__Vclkskip" + cvtToStr(idNum) + "_r", 1);
            std::vector<AstVarScope*> shadows;
            for (size_t i = 0; i < item.m_inputs.size(); ++i) {
                shadows.push_back(scopep->createTempLike(
                    "__Vclkskip" + cvtToStr(idNum) + "_s" + cvtToStr(i), item.m_inputs[i]));
            }
            addList(prologp, new AstAssign{flp, new AstVarRef{flp, runp, VAccess::WRITE},
                                           differCond(flp, initedp, item.m_inputs, shadows)});
            AstIf* const samplep = new AstIf{flp, new AstVarRef{flp, runp, VAccess::READ}};
            samplep->addThensp(sampleBody(flp, initedp, item.m_inputs, shadows));
            addList(prologp, samplep);
            for (AstNode* const stmtp : item.m_stmts) {
                AstIf* const ifp
                    = new AstIf{stmtp->fileline(), new AstVarRef{stmtp->fileline(), runp, VAccess::READ}};
                stmtp->replaceWith(ifp);
                ifp->addThensp(stmtp);
            }
            counted.insert(item.m_id);
            UINFO(4, "ClkSkip guard " << item.m_id << " inputs=" << item.m_inputs.size()
                                      << " stmts=" << item.m_stmts.size() << " in " << funcp->name()
                                      << endl);
        }
        if (prologp) funcp->stmtsp()->addHereThisAsNext(prologp);
    }

    V3Stats::addStat("Optimizations, Clock skip scopes", counted.size());
    V3Global::dumpCheckGlobalTree("clkskip", 0, dumpTree() >= 3);
}
