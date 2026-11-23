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
#include "V3PartitionGraph.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>
#include <queue>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

constexpr int kMaxInputs = 64;
constexpr int kMaxBits = 4096;

bool guardFuncName(const string& name) {
    if (name.rfind("_ico_", 0) == 0) return true;
    // Multi-domain combo keeps the _comb tag in the active and NBA regions.
    // A single-clock sequent function also holds the edge update, so it stays.
    return name.find("_comb__") != string::npos;
}

bool impureNode(const AstNode* nodep) {
    if (!nodep->isPure() || nodep->isTimingControl()) return true;
    if (VN_IS(nodep, NodeStmt) && !VN_IS(nodep, Assign) && !VN_IS(nodep, AssignW)
        && !VN_IS(nodep, If) && !VN_IS(nodep, Comment)) return true;
    return VN_IS(nodep, CExpr) || VN_IS(nodep, CCall) || VN_IS(nodep, CMethodHard)
           || VN_IS(nodep, CMethodCall) || VN_IS(nodep, CNew) || VN_IS(nodep, UCFunc)
           || VN_IS(nodep, FuncRef)
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

bool externallyMutable(const AstVarScope* vscp) {
    const AstVar* const varp = vscp->varp();
    return varp->isPrimaryIO() || varp->isSigPublic() || varp->isForceable()
           || varp->isWrittenByDpi() || varp->isWrittenBySuspendable()
           || varp->isUsedVirtIface() || varp->isClassMember() || varp->isSc()
           || varp->isFuncLocal() || varp->direction() == VDirection::INOUT;
}

struct BitRange final {
    int m_lsb;
    int m_width;

    void include(const BitRange& other) {
        const int end = std::max(m_lsb + m_width, other.m_lsb + other.m_width);
        m_lsb = std::min(m_lsb, other.m_lsb);
        m_width = end - m_lsb;
    }
    bool overlaps(const BitRange& other) const {
        return m_lsb < other.m_lsb + other.m_width && other.m_lsb < m_lsb + m_width;
    }
    static bool fixedSelect(const AstSel* selp) {
        const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
        const AstConst* const widthp = VN_CAST(selp->widthp(), Const);
        if (!lsbp || !widthp || lsbp->num().isFourState() || widthp->num().isFourState()) {
            return false;
        }
        const int lsb = selp->lsbConst();
        const int width = selp->widthConst();
        const int fromWidth = selp->fromp()->width();
        return lsb >= 0 && width > 0 && width <= fromWidth && lsb <= fromWidth - width;
    }
    static BitRange of(const AstVarRef* refp) {
        const BitRange full{0, refp->varp()->width()};
        BitRange result = full;
        const AstNode* exprp = refp;
        while (true) {
            const AstNode* parentp = exprp;
            while (parentp->backp() && parentp->backp()->nextp() == parentp) {
                parentp = parentp->backp();
            }
            const AstSel* const selp = VN_CAST(parentp->backp(), Sel);
            if (!selp || selp->fromp() != exprp) return result;
            if (!fixedSelect(selp)) return full;
            result.m_lsb += selp->lsbConst();
            result.m_width = selp->widthConst();
            exprp = selp;
        }
    }
};

struct WriteIndex final {
    struct Writer final {
        AstNodeAssign* m_assignp;
        BitRange m_range;
    };
    std::unordered_map<AstVarScope*, std::vector<Writer>> m_writers;
    std::vector<AstNodeAssign*> m_assigns;
    std::unordered_set<AstVarScope*> m_untracked;
    std::unordered_map<AstNodeAssign*, std::vector<AstVarScope*>> m_invalidations;

    explicit WriteIndex(AstNetlist* netlistp) {
        std::unordered_set<const AstVarRef*> covered;
        netlistp->foreach([&](AstNodeAssign* assignp) {
            m_assigns.push_back(assignp);
            assignp->lhsp()->foreach([&](AstVarRef* refp) {
                if (!refp->varScopep() || !refp->access().isWriteOrRW()) return;
                covered.insert(refp);
                auto& writers = m_writers[refp->varScopep()];
                if (writers.empty() || writers.back().m_assignp != assignp) {
                    writers.push_back({assignp, BitRange::of(refp)});
                } else {
                    writers.back().m_range.include(BitRange::of(refp));
                }
            });
        });
        netlistp->foreach([&](AstVarRef* refp) {
            if (refp->varScopep() && refp->access().isWriteOrRW() && !covered.count(refp)) {
                m_untracked.insert(refp->varScopep());
            }
        });
        // Hierarchical probes need no case of their own: V3LinkDot rewrites every
        // AstVarXRef into a scoped AstVarRef at scope creation, so a probe into a
        // cached scope is an ordinary read of an indexed variable here.
        // Opaque C text (DPI marshalling, $c) may touch a variable it names as a
        // node without an assignment the index can see. Every variable referenced
        // under such a node is untracked; a text-only mention of a model variable
        // by name does not occur outside the threaded/timing/trace paths, which are
        // refused or read-only.
        const auto untrackUnder = [&](AstNode* nodep) {
            nodep->foreach([&](AstNodeVarRef* refp) {
                if (refp->varScopep() && m_untracked.insert(refp->varScopep()).second) {
                    V3Stats::addStatSum("Optimizations, Clock skip opaque-text variables", 1);
                }
            });
        };
        netlistp->foreach([&](AstCStmt* nodep) { untrackUnder(nodep); });
        netlistp->foreach([&](AstCExpr* nodep) { untrackUnder(nodep); });
        netlistp->foreach([&](AstUCFunc* nodep) { untrackUnder(nodep); });
    }

    bool tracked(AstVarScope* vscp) const {
        return !externallyMutable(vscp) && !m_untracked.count(vscp);
    }

    void subscribe(AstVarScope* vscp, AstVarScope* validp, const BitRange& range,
                   const std::unordered_set<AstNodeAssign*>& own) {
        const auto it = m_writers.find(vscp);
        if (it == m_writers.end()) return;
        for (const Writer& writer : it->second) {
            if (own.count(writer.m_assignp)) continue;
            if (!range.overlaps(writer.m_range)) {
                V3Stats::addStatSum("Optimizations, Clock skip disjoint subscriptions", 1);
                continue;
            }
            auto& flags = m_invalidations[writer.m_assignp];
            if (std::find(flags.begin(), flags.end(), validp) == flags.end()) flags.push_back(validp);
        }
    }

    void emit() {
        unsigned seq = 0;
        for (AstNodeAssign* const assignp : m_assigns) {
            const auto it = m_invalidations.find(assignp);
            if (it == m_invalidations.end()) continue;
            const auto& entry = *it;
            AstNode* updatesp = nullptr;
            FileLine* const flp = entry.first->fileline();
            for (AstVarScope* const flagp : entry.second) {
                addList(updatesp, new AstAssign{flp, new AstVarRef{flp, flagp, VAccess::WRITE},
                                               new AstConst{flp, AstConst::BitFalse{}}});
                V3Stats::addStatSum("Optimizations, Clock skip invalidation edges", 1);
            }
            AstNodeExpr* const lhsp = entry.first->lhsp();
            AstNodeExpr* basep = lhsp;
            bool fixed = true;
            while (AstSel* const selp = VN_CAST(basep, Sel)) {
                fixed &= BitRange::fixedSelect(selp);
                basep = selp->fromp();
            }
            AstVarRef* const refp = VN_CAST(basep, VarRef);
            AstCFunc* const funcp = enclosingFunc(entry.first);
            if (fixed && refp && funcp && funcp->scopep() && lhsp->width() <= VL_QUADSIZE
                && comparableInput(refp->varScopep())
                && BitRange::of(refp).m_width == lhsp->width()) {
                const auto readLhs = [&]() {
                    AstNodeExpr* const resultp = lhsp->cloneTree(false);
                    resultp->foreach([](AstVarRef* refp) { refp->access(VAccess::READ); });
                    return resultp;
                };
                AstVarScope* const oldp = funcp->scopep()->createTemp(
                    "__Vclkskip_old" + cvtToStr(seq++), lhsp->dtypep());
                oldp->trace(false);
                oldp->varp()->trace(false);
                entry.first->addHereThisAsNext(new AstAssign{
                    flp, new AstVarRef{flp, oldp, VAccess::WRITE}, readLhs()});
                entry.first->addNextHere(new AstIf{
                    flp, new AstNeq{flp, new AstVarRef{flp, oldp, VAccess::READ}, readLhs()}, updatesp});
                V3Stats::addStatSum("Optimizations, Clock skip change-filtered stores", 1);
            } else {
                entry.first->addHereThisAsNext(updatesp);
            }
        }
    }
};

struct InstGroup final {
    std::vector<AstNode*> m_stmts;
    std::vector<AstVarScope*> m_reads;
    std::unordered_set<AstVarScope*> m_readSet;
    std::unordered_set<AstVarScope*> m_writes;
    std::unordered_set<AstVarScope*> m_defined;
    std::unordered_map<AstVarScope*, BitRange> m_readRanges;
    std::unordered_map<AstVarScope*, BitRange> m_writeRanges;
    bool m_refuse = false;
    string m_why;
    static void noteRange(std::unordered_map<AstVarScope*, BitRange>& ranges,
                          const AstVarRef* refp) {
        const BitRange range = BitRange::of(refp);
        const auto inserted = ranges.emplace(refp->varScopep(), range);
        if (!inserted.second) inserted.first->second.include(range);
    }
    void noteRead(const AstVarRef* refp) {
        AstVarScope* const vscp = refp->varScopep();
        if (m_defined.count(vscp)) return;
        if (m_readSet.insert(vscp).second) m_reads.push_back(vscp);
        noteRange(m_readRanges, refp);
    }
    void noteWrite(const AstVarRef* refp) {
        m_writes.insert(refp->varScopep());
        noteRange(m_writeRanges, refp);
    }
    void noteDefinition(AstNode* stmtp) {
        if (VN_IS(stmtp, Assign) || VN_IS(stmtp, AssignW)) {
            const AstNodeAssign* const assignp = VN_AS(stmtp, NodeAssign);
            if (const AstVarRef* const refp = VN_CAST(assignp->lhsp(), VarRef)) {
                m_defined.insert(refp->varScopep());
            }
        }
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

    // Model-wide refusals, each named in the stats so a real-model build says
    // which one fired. Threads and timing need an ordering proof this pass does
    // not carry. Opaque C text and hierarchical references are handled per
    // variable by the write index below, not by refusing the model.
    const char* unsupported = nullptr;
    if (v3Global.opt.threads() > 1) {
        unsupported = "threads";
    } else if (v3Global.usesTiming()) {
        unsupported = "timing";
    }
    if (unsupported) {
        V3Stats::addStat("Optimizations, Clock skip unsupported model", 1);
        V3Stats::addStat(string{"Optimizations, Clock skip unsupported model ("} + unsupported + ")", 1);
        return;
    }
    AstCFunc* initp = nullptr;
    for (AstCFunc* const funcp : funcs) {
        if (funcp->name() == "_eval_static") initp = funcp;
    }
    if (!initp) return;
    WriteIndex writes{netlistp};
    const auto arm = [&](AstVarScope* validp, const InstGroup& inst) {
        validp->trace(false);
        validp->varp()->trace(false);
        validp->varp()->noSubst(true);
        initp->addInitsp(new AstAssign{validp->fileline(),
                                     new AstVarRef{validp->fileline(), validp, VAccess::WRITE},
                                     new AstConst{validp->fileline(), AstConst::BitFalse{}}});
        std::unordered_set<AstNodeAssign*> own;
        for (AstNode* const stmtp : inst.m_stmts) {
            stmtp->foreach([&](AstNodeAssign* assignp) { own.insert(assignp); });
        }
        for (AstVarScope* const vscp : inst.m_reads) {
            if (writes.tracked(vscp)) {
                writes.subscribe(vscp, validp, inst.m_readRanges.at(vscp), own);
            }
        }
        for (AstVarScope* const vscp : inst.m_writes) {
            writes.subscribe(vscp, validp, inst.m_writeRanges.at(vscp), own);
        }
    };
    std::unordered_set<string> counted;
    int seq = 0;

    for (AstCFunc* const funcp : funcs) {
        if (!funcp->scopep() || !funcp->stmtsp() || !guardFuncName(funcp->name())) continue;
        // Inlined logic lives in the top scope, mixed across instances.
        // A non-top function is already one instance; its call is guarded.
        const bool splitInstances = funcp->scopep()->isTop();
        if (!splitInstances && (funcp->initsp() || funcp->finalsp() || funcp->argsp()
                                || !funcp->argTypes().empty())) continue;

        std::vector<AstNode*> stmts;
        for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) stmts.push_back(stmtp);

        std::vector<string> order;
        std::unordered_map<string, InstGroup> groups;
        string previousId;
        string currentKey;
        unsigned run = 0;
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
                inst.m_stmts.push_back(stmtp);
                if (impure || unscoped) {
                    inst.m_refuse = true;
                    inst.m_why = impure ? "impure combo" : "unscoped reference";
                }
                for (AstVarRef* const refp : refs) {
                    if (!refp->varScopep()) continue;
                    if (refp->access().isWriteOrRW()) inst.noteWrite(refp);
                    if (refp->access().isReadOrRW()) inst.noteRead(refp);
                }
                inst.noteDefinition(stmtp);
                continue;
            }

            const string id = statementInstance(ids);
            if (impure || unscoped || id.empty()) {
                previousId.clear();
                continue;
            }

            if (id != previousId) {
                currentKey = id + "#" + cvtToStr(run++);
                previousId = id;
            }
            InstGroup& inst = groupOf(currentKey);
            inst.m_stmts.push_back(stmtp);
            for (AstVarRef* const refp : refs) {
                if (refp->access().isWriteOrRW()) inst.noteWrite(refp);
                if (refp->access().isReadOrRW()) inst.noteRead(refp);
            }
            inst.noteDefinition(stmtp);
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
            bool refuse = inst.m_writes.empty() || inst.m_reads.size() > kMaxInputs;
            for (AstVarScope* const vscp : inst.m_writes) {
                if (!writes.tracked(vscp) || !comparableInput(vscp)) refuse = true;
            }
            for (AstVarScope* const vscp : inst.m_reads) {
                if (inst.m_writes.count(vscp) || vscp->varp()->isFuncLocal()) {
                    refuse = true;
                    UINFO(4, "ClkSkip refuse " << id << ": feedback or local input" << endl);
                    break;
                }
                if (vscp->varp()->isParam()) continue;
                if (!comparableInput(vscp)) {
                    refuse = true;
                    UINFO(4, "ClkSkip refuse " << id << ": non-integral input" << endl);
                    break;
                }
                if (writes.tracked(vscp)) continue;
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
            arm(initedp, groups.at(ready[0].m_id));
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

        for (const Ready& item : ready) {
            const int idNum = seq++;
            AstVarScope* const initedp = scopep->createTemp("__Vclkskip" + cvtToStr(idNum) + "_i", 1);
            arm(initedp, groups.at(item.m_id));
            std::vector<AstVarScope*> shadows;
            for (size_t i = 0; i < item.m_inputs.size(); ++i) {
                shadows.push_back(scopep->createTempLike(
                    "__Vclkskip" + cvtToStr(idNum) + "_s" + cvtToStr(i), item.m_inputs[i]));
            }
            AstIf* const ifp = new AstIf{flp, differCond(flp, initedp, item.m_inputs, shadows)};
            ifp->addThensp(sampleBody(flp, initedp, item.m_inputs, shadows));
            item.m_stmts.front()->replaceWith(ifp);
            for (AstNode* const stmtp : item.m_stmts) {
                if (stmtp->backp()) stmtp->unlinkFrBack();
                ifp->addThensp(stmtp);
            }
            counted.insert(item.m_id.substr(0, item.m_id.find('#')));
            V3Stats::addStatSum("Optimizations, Clock skip execution groups", 1);
            V3Stats::addStatSum("Optimizations, Clock skip external compares", item.m_inputs.size());
            UINFO(4, "ClkSkip guard " << item.m_id << " inputs=" << item.m_inputs.size()
                                      << " stmts=" << item.m_stmts.size() << " in " << funcp->name()
                                      << endl);
        }
    }
    writes.emit();

    V3Stats::addStat("Optimizations, Clock skip scopes", counted.size());
    V3Global::dumpCheckGlobalTree("clkskip", 0, dumpTree() >= 3);
}

namespace {

bool impureForSink(const AstNode* nodep) {
    if (!nodep->isPure() || nodep->isTimingControl()) return true;
    if (VN_IS(nodep, NodeStmt) && !VN_IS(nodep, Assign) && !VN_IS(nodep, AssignW)
        && !VN_IS(nodep, If) && !VN_IS(nodep, Comment) && !VN_IS(nodep, CReset)
        && !VN_IS(nodep, JumpBlock) && !VN_IS(nodep, JumpLabel) && !VN_IS(nodep, JumpGo)) {
        return true;
    }
    return VN_IS(nodep, CExpr) || VN_IS(nodep, CCall) || VN_IS(nodep, CMethodHard)
           || VN_IS(nodep, CMethodCall) || VN_IS(nodep, CNew) || VN_IS(nodep, UCFunc)
           || VN_IS(nodep, FuncRef) || VN_IS(nodep, TaskRef) || VN_IS(nodep, VarXRef)
           || VN_IS(nodep, Display) || VN_IS(nodep, Finish) || VN_IS(nodep, Stop)
           || VN_IS(nodep, MonitorOff) || VN_IS(nodep, FOpen) || VN_IS(nodep, FClose)
           || VN_IS(nodep, ReadMem) || VN_IS(nodep, WriteMem) || VN_IS(nodep, Rand)
           || VN_IS(nodep, CStmt) || VN_IS(nodep, AssignDly) || VN_IS(nodep, SysFuncAsTask)
           || VN_IS(nodep, Time) || VN_IS(nodep, Assert) || VN_IS(nodep, CoverInc)
           || VN_IS(nodep, CoverToggle) || VN_IS(nodep, FireEvent) || VN_IS(nodep, Sampled);
}

bool parseTriggerCond(AstNodeExpr* condp, AstVarScope*& trigVscp, std::set<uint32_t>& bits) {
    if (AstOr* const orp = VN_CAST(condp, Or)) {
        return parseTriggerCond(orp->lhsp(), trigVscp, bits)
               && parseTriggerCond(orp->rhsp(), trigVscp, bits);
    }
    AstCMethodHard* const callp = VN_CAST(condp, CMethodHard);
    if (!callp) return false;
    AstVarRef* const refp = VN_CAST(callp->fromp(), VarRef);
    if (!refp || !refp->varScopep()) return false;
    const AstBasicDType* const basicp = refp->varScopep()->dtypep()->basicp();
    if (!basicp || !basicp->isTriggerVec()) return false;
    if (!trigVscp) {
        trigVscp = refp->varScopep();
    } else if (trigVscp != refp->varScopep()) {
        return false;
    }
    if (callp->name() == "at") {
        AstConst* const idxp = VN_CAST(callp->pinsp(), Const);
        if (!idxp || idxp->nextp() || idxp->num().isFourState()) return false;
        bits.insert(idxp->toUInt());
        return true;
    }
    if (callp->name() == "wordAny") {
        AstConst* const wordp = VN_CAST(callp->pinsp(), Const);
        AstConst* const maskp = wordp ? VN_CAST(wordp->nextp(), Const) : nullptr;
        if (!wordp || !maskp || maskp->nextp() || wordp->num().isFourState()
            || maskp->num().isFourState()) {
            return false;
        }
        const uint32_t base = wordp->toUInt() * 64U;
        uint64_t mask = maskp->toUQuad();
        if (!mask) return false;
        while (mask) {
            const uint32_t bit = static_cast<uint32_t>(__builtin_ctzll(mask));
            bits.insert(base + bit);
            mask &= (mask - 1ULL);
        }
        return true;
    }
    return false;
}

AstNodeExpr* buildTriggerCond(FileLine* flp, AstVarScope* trigVscp,
                              const std::set<uint32_t>& bits) {
    std::map<uint32_t, uint64_t> words;
    for (const uint32_t idx : bits) words[idx / 64U] |= (uint64_t{1} << (idx % 64U));
    AstNodeExpr* eqnp = nullptr;
    for (const auto& entry : words) {
        const uint32_t word = entry.first;
        uint64_t mask = entry.second;
        if (v3Global.opt.fTriggerWords() && __builtin_popcountll(mask) > 1) {
            AstConst* const wp = new AstConst{flp, word};
            wp->addNext(new AstConst{flp, AstConst::Unsized64{}, mask});
            AstCMethodHard* const testp = new AstCMethodHard{
                flp, new AstVarRef{flp, trigVscp, VAccess::READ}, "wordAny", wp};
            testp->dtypeSetBit();
            testp->pure(true);
            eqnp = eqnp ? static_cast<AstNodeExpr*>(new AstOr{flp, eqnp, testp}) : testp;
        } else {
            while (mask) {
                const uint32_t bit = static_cast<uint32_t>(__builtin_ctzll(mask));
                const uint32_t idx = word * 64U + bit;
                AstCMethodHard* const testp = new AstCMethodHard{
                    flp, new AstVarRef{flp, trigVscp, VAccess::READ}, "at",
                    new AstConst{flp, idx}};
                testp->dtypeSetBit();
                testp->pure(true);
                eqnp = eqnp ? static_cast<AstNodeExpr*>(new AstOr{flp, eqnp, testp}) : testp;
                mask &= (mask - 1ULL);
            }
        }
    }
    return eqnp;
}

struct NbaEntry final {
    AstIf* m_ifp = nullptr;
    AstStmtExpr* m_stmtp = nullptr;
    AstCCall* m_callp = nullptr;
    AstCFunc* m_calleep = nullptr;
    std::set<uint32_t> m_triggers;
    size_t m_order = 0;
    bool m_candidate = false;
    bool m_pinned = true;
    std::vector<AstVarScope*> m_reads;
    std::vector<AstVarScope*> m_writes;
    std::set<uint32_t> m_sinks;
};

void collectNbaEntries(AstNode* stmtsp, std::vector<NbaEntry>& entries,
                       std::unordered_set<const AstCFunc*>& dispatchFuncs,
                       std::unordered_set<const AstCFunc*>& leafFuncs,
                       std::unordered_set<AstVarScope*>& pinnedVars,
                       AstVarScope*& nbaTrigVscp) {
    for (AstNode* nodep = stmtsp; nodep; nodep = nodep->nextp()) {
        if (AstExecGraph* const graphp = VN_CAST(nodep, ExecGraph)) {
            // Walk MTasks in deterministic topological order (Kahn's algorithm,
            // tie-broken by ExecMTask::id()).
            std::unordered_map<const ExecMTask*, uint32_t> indeg;
            std::unordered_map<uint32_t, const ExecMTask*> byId;
            for (const V3GraphVertex* vxp = graphp->depGraphp()->verticesBeginp(); vxp;
                 vxp = vxp->verticesNextp()) {
                const auto* const mtp = dynamic_cast<const ExecMTask*>(vxp);
                if (!mtp) continue;
                uint32_t d = 0;
                for (const V3GraphEdge* ep = mtp->inBeginp(); ep; ep = ep->inNextp()) ++d;
                indeg[mtp] = d;
                byId[mtp->id()] = mtp;
            }
            std::priority_queue<uint32_t, std::vector<uint32_t>, std::greater<uint32_t>> ready;
            for (const auto& kv : indeg) {
                if (kv.second == 0) ready.push(kv.first->id());
            }
            while (!ready.empty()) {
                const ExecMTask* const mtp = byId.at(ready.top());
                ready.pop();
                if (mtp->bodyp()) {
                    collectNbaEntries(mtp->bodyp()->stmtsp(), entries, dispatchFuncs, leafFuncs,
                                      pinnedVars, nbaTrigVscp);
                }
                for (const V3GraphEdge* ep = mtp->outBeginp(); ep; ep = ep->outNextp()) {
                    const auto* const nxtp = dynamic_cast<const ExecMTask*>(ep->top());
                    if (!nxtp) continue;
                    if (--indeg[nxtp] == 0) ready.push(nxtp->id());
                }
            }
            continue;
        }
        if (AstStmtExpr* const stmtp = VN_CAST(nodep, StmtExpr)) {
            AstCCall* const callp = VN_CAST(stmtp->exprp(), CCall);
            if (callp && callp->funcp() && callp->funcp()->name().rfind("_eval_nba__", 0) == 0) {
                dispatchFuncs.insert(callp->funcp());
                collectNbaEntries(callp->funcp()->stmtsp(), entries, dispatchFuncs, leafFuncs,
                                  pinnedVars, nbaTrigVscp);
                continue;
            }
        }
        if (AstIf* const ifp = VN_CAST(nodep, If)) {
            std::set<uint32_t> trigs;
            if (!ifp->elsesp() && parseTriggerCond(ifp->condp(), nbaTrigVscp, trigs)
                && !trigs.empty()) {
                for (AstNode* sp = ifp->thensp(); sp; sp = sp->nextp()) {
                    AstStmtExpr* const sep = VN_CAST(sp, StmtExpr);
                    AstCCall* const callp = sep ? VN_CAST(sep->exprp(), CCall) : nullptr;
                    if (callp && callp->funcp()) {
                        NbaEntry e;
                        e.m_ifp = ifp;
                        e.m_stmtp = sep;
                        e.m_callp = callp;
                        e.m_calleep = callp->funcp();
                        e.m_triggers = trigs;
                        e.m_order = entries.size();
                        leafFuncs.insert(e.m_calleep);
                        entries.push_back(std::move(e));
                    } else {
                        // Inline statement inside triggered NBA block: record as non-candidate
                        // reader/writer at trigger set `trigs` (writes pinned, reads sinked).
                        NbaEntry e;
                        e.m_ifp = ifp;
                        e.m_triggers = trigs;
                        e.m_order = entries.size();
                        sp->foreach([&](AstVarRef* refp) {
                            AstVarScope* const vscp = refp->varScopep();
                            if (!vscp || vscp->varp()->isFuncLocal()) return;
                            if (refp->access().isWriteOrRW()) pinnedVars.insert(vscp);
                            if (refp->access().isReadOrRW()) e.m_reads.push_back(vscp);
                        });
                        entries.push_back(std::move(e));
                    }
                }
                continue;
            }
        }
        // Any other unguarded statement inside _eval_nba pins all referenced variables.
        nodep->foreach([&](AstNodeVarRef* refp) {
            if (refp->varScopep()) pinnedVars.insert(refp->varScopep());
        });
    }
}

bool setIntersects(const std::set<uint32_t>& a, const std::set<uint32_t>& b) {
    auto ia = a.begin();
    auto ib = b.begin();
    while (ia != a.end() && ib != b.end()) {
        if (*ia == *ib) return true;
        if (*ia < *ib) ++ia;
        else ++ib;
    }
    return false;
}

std::set<uint32_t> setIntersection(const std::set<uint32_t>& a, const std::set<uint32_t>& b) {
    std::set<uint32_t> out;
    auto ia = a.begin();
    auto ib = b.begin();
    while (ia != a.end() && ib != b.end()) {
        if (*ia == *ib) {
            out.insert(*ia);
            ++ia;
            ++ib;
        } else if (*ia < *ib) {
            ++ia;
        } else {
            ++ib;
        }
    }
    return out;
}

}  // namespace

void V3ClkSkip::clkSkipSinkAll(AstNetlist* netlistp) {
    UINFO(4, __FUNCTION__ << ": " << endl);

    if (v3Global.usesTiming()) {
        V3Stats::addStat("Optimizations, Clock skip sink unsupported model (timing)", 1);
        return;
    }

    AstCFunc* const evalp = netlistp->evalp();
    AstCFunc* const evalNbap = netlistp->evalNbap();
    if (!evalp || !evalNbap) return;

    AstCFunc* staticInitp = nullptr;
    std::vector<AstCFunc*> allFuncs;
    std::unordered_map<const AstCFunc*, size_t> callCount;
    netlistp->foreach([&](AstCFunc* funcp) {
        allFuncs.push_back(funcp);
        if (funcp->name() == "_eval_static") staticInitp = funcp;
    });
    netlistp->foreach([&](AstCCall* callp) {
        if (callp->funcp()) ++callCount[callp->funcp()];
    });
    if (!staticInitp) return;

    // Locate the unique call to _eval_nba inside _eval.
    std::vector<AstStmtExpr*> nbaCallsInEval;
    evalp->foreach([&](AstCCall* callp) {
        if (callp->funcp() != evalNbap) return;
        if (AstStmtExpr* const sep = VN_CAST(callp->backp(), StmtExpr)) {
            if (sep->exprp() == callp) nbaCallsInEval.push_back(sep);
        }
    });
    if (nbaCallsInEval.size() != 1) return;
    AstStmtExpr* const nbaCallStmtp = nbaCallsInEval.front();

    // 1. Collect all NBA entries in deterministic topological order.
    std::vector<NbaEntry> entries;
    std::unordered_set<const AstCFunc*> nbaDispatchFuncs{evalNbap};
    std::unordered_set<const AstCFunc*> nbaLeafFuncs;
    std::unordered_set<AstVarScope*> pinnedVars;
    AstVarScope* nbaTrigVscp = nullptr;
    collectNbaEntries(evalNbap->stmtsp(), entries, nbaDispatchFuncs, nbaLeafFuncs, pinnedVars,
                      nbaTrigVscp);
    if (!nbaTrigVscp || entries.empty()) return;

    // 2. Pin variables observed outside _eval_nba during simulation.
    //    Ignore time-0 only / debug-dump roots (_eval_static, _eval_initial,
    //    _eval_settle, _eval_stl, _eval_triggers__stl, _ctor_var_reset, _dump_triggers__).
    const auto isInitOrSettleRoot = [](const AstCFunc* funcp) {
        const string& n = funcp->name();
        return n == "_eval_static" || n == "_eval_initial" || n == "_eval_settle"
               || n == "_eval_stl" || n == "_eval_triggers__stl" || n == "_ctor_var_reset"
               || n.rfind("_dump_triggers__", 0) == 0 || n.rfind("_stl_", 0) == 0
               || n.rfind("_eval_initial__", 0) == 0 || n.rfind("_eval_static__", 0) == 0
               || n.rfind("_ctor_var_reset", 0) == 0;
    };
    std::unordered_set<const AstCFunc*> nonNbaLiveFuncs;
    std::vector<const AstCFunc*> work;
    const auto enqueueLive = [&](const AstCFunc* fp) {
        if (!fp || nbaDispatchFuncs.count(fp) || nbaLeafFuncs.count(fp)) return;
        if (nonNbaLiveFuncs.insert(fp).second) work.push_back(fp);
    };
    enqueueLive(evalp);
    for (const AstCFunc* const fp : allFuncs) {
        if (fp == evalNbap || isInitOrSettleRoot(fp)) continue;
        if (fp->entryPoint() || fp->dpiExportImpl() || fp->dpiExportDispatcher()
            || fp->name() == "_eval_final") {
            enqueueLive(fp);
        }
    }
    while (!work.empty()) {
        const AstCFunc* const fp = work.back();
        work.pop_back();
        const_cast<AstCFunc*>(fp)->foreach([&](AstNode* nodep) {
            if (AstCCall* const callp = VN_CAST(nodep, CCall)) {
                if (callp->funcp() && callp->funcp() != evalNbap) enqueueLive(callp->funcp());
            } else if (AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
                if (refp->varScopep() && !refp->varScopep()->varp()->isFuncLocal()) {
                    pinnedVars.insert(refp->varScopep());
                }
            }
        });
    }
    // Pin any variable touched by opaque C text, external mutability, latches, or tracing.
    const auto pinOpaque = [&](AstNode* nodep) {
        nodep->foreach([&](AstNodeVarRef* refp) {
            if (refp->varScopep()) pinnedVars.insert(refp->varScopep());
        });
    };
    netlistp->foreach([&](AstCStmt* nodep) { pinOpaque(nodep); });
    netlistp->foreach([&](AstCExpr* nodep) { pinOpaque(nodep); });
    netlistp->foreach([&](AstUCFunc* nodep) { pinOpaque(nodep); });
    netlistp->foreach([&](AstVarScope* vscp) {
        const AstVar* const varp = vscp->varp();
        if (externallyMutable(vscp) || varp->isLatched()
            || (v3Global.opt.trace() && (vscp->isTrace() || varp->isTrace()))) {
            pinnedVars.insert(vscp);
        }
    });

    // 3. Classify each NBA entry and collect read/write sets.
    std::unordered_map<AstVarScope*, std::vector<size_t>> candWriters;
    for (size_t idx = 0; idx < entries.size(); ++idx) {
        NbaEntry& e = entries[idx];
        if (!e.m_calleep) continue;
        AstCFunc* const fp = e.m_calleep;
        bool pure = fp->name().find("_nba_comb__") != string::npos
                    && callCount[fp] == 1 && !fp->argsp() && fp->argTypes().empty()
                    && e.m_triggers.size() >= 2;
        if (pure) {
            fp->foreach([&](const AstNode* nodep) {
                if (nodep != fp && impureForSink(nodep)) pure = false;
            });
        }
        std::unordered_set<AstVarScope*> rset, wset;
        fp->foreach([&](AstVarRef* refp) {
            AstVarScope* const vscp = refp->varScopep();
            if (!vscp) {
                pure = false;
                return;
            }
            if (vscp->varp()->isFuncLocal()) return;
            if (refp->access().isWriteOrRW()) wset.insert(vscp);
            if (refp->access().isReadOrRW()) rset.insert(vscp);
        });
        e.m_reads.assign(rset.begin(), rset.end());
        e.m_writes.assign(wset.begin(), wset.end());
        if (pure && !e.m_writes.empty()) {
            e.m_candidate = true;
            e.m_pinned = false;
            for (AstVarScope* const vscp : e.m_writes) candWriters[vscp].push_back(idx);
        } else {
            e.m_candidate = false;
            e.m_pinned = true;
            for (AstVarScope* const vscp : e.m_writes) pinnedVars.insert(vscp);
        }
    }

    // 4. Backward fixed-point over sink trigger sets.
    std::unordered_map<AstVarScope*, std::set<uint32_t>> varSinks;
    for (const NbaEntry& e : entries) {
        if (!e.m_pinned) continue;
        for (AstVarScope* const vscp : e.m_reads) {
            varSinks[vscp].insert(e.m_triggers.begin(), e.m_triggers.end());
        }
    }

    const auto pinEntry = [&](NbaEntry& e) {
        if (e.m_pinned) return false;
        e.m_pinned = true;
        e.m_sinks.clear();
        for (AstVarScope* const vscp : e.m_writes) pinnedVars.insert(vscp);
        for (AstVarScope* const vscp : e.m_reads) {
            varSinks[vscp].insert(e.m_triggers.begin(), e.m_triggers.end());
        }
        return true;
    };

    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t idx = 0; idx < entries.size(); ++idx) {
            NbaEntry& e = entries[idx];
            if (e.m_pinned) continue;

            // Check whether any written variable is pinned, and union sinks of all outputs.
            bool anyPinned = false;
            std::set<uint32_t> outSinks;
            for (AstVarScope* const vscp : e.m_writes) {
                if (pinnedVars.count(vscp)) {
                    anyPinned = true;
                    break;
                }
                const auto it = varSinks.find(vscp);
                if (it != varSinks.end()) outSinks.insert(it->second.begin(), it->second.end());
            }
            if (anyPinned) {
                if (pinEntry(e)) changed = true;
                continue;
            }
            if (outSinks.empty()) continue;

            // Effective triggers = intersection of driving triggers and sink triggers.
            // Ensure every deferred producer we read belongs to the exact same group:
            // if a read var is written by another candidate whose sinks contain triggers
            // outside `eff`, absorb them (or pin if no strict subset remains).
            std::set<uint32_t> eff = setIntersection(e.m_triggers, outSinks);
            // Also unify with any co-writers of our outputs or deferred producers of our inputs.
            for (AstVarScope* const r : e.m_reads) {
                if (pinnedVars.count(r)) continue;
                const auto wit = candWriters.find(r);
                if (wit == candWriters.end()) continue;
                for (const size_t widx : wit->second) {
                    if (widx == idx || entries[widx].m_pinned) continue;
                    const auto& ws = entries[widx].m_sinks;
                    if (!ws.empty()) eff.insert(ws.begin(), ws.end());
                }
            }
            eff = setIntersection(e.m_triggers, eff);

            if (eff.empty() || eff.size() >= e.m_triggers.size()) {
                if (pinEntry(e)) changed = true;
                continue;
            }
            if (eff != e.m_sinks) {
                e.m_sinks = std::move(eff);
                for (AstVarScope* const vscp : e.m_reads) {
                    varSinks[vscp].insert(e.m_sinks.begin(), e.m_sinks.end());
                }
                for (AstVarScope* const vscp : e.m_writes) {
                    varSinks[vscp].insert(e.m_sinks.begin(), e.m_sinks.end());
                }
                changed = true;
            }
        }
        // Final consistency: any remaining unpinned entry with empty sinks (dead write)
        // or reading a deferred producer from a mismatched group gets pinned.
        if (!changed) {
            for (size_t idx = 0; idx < entries.size(); ++idx) {
                NbaEntry& e = entries[idx];
                if (e.m_pinned) continue;
                bool bad = e.m_sinks.empty();
                for (AstVarScope* const vscp : e.m_writes) {
                    if (pinnedVars.count(vscp)) bad = true;
                    const auto wit = candWriters.find(vscp);
                    if (wit != candWriters.end()) {
                        for (const size_t widx : wit->second) {
                            if (entries[widx].m_pinned || entries[widx].m_sinks != e.m_sinks) {
                                bad = true;
                            }
                        }
                    }
                }
                for (AstVarScope* const r : e.m_reads) {
                    if (pinnedVars.count(r)) continue;
                    const auto wit = candWriters.find(r);
                    if (wit == candWriters.end()) continue;
                    for (const size_t widx : wit->second) {
                        if (widx == idx) continue;
                        if (!entries[widx].m_pinned && entries[widx].m_sinks != e.m_sinks) {
                            bad = true;
                        }
                    }
                }
                if (bad && pinEntry(e)) changed = true;
            }
        }
    }

    // 5. Group deferred entries by their narrowed sink trigger set K.
    struct SinkGroup final {
        std::set<uint32_t> m_keep;
        std::set<uint32_t> m_dropped;
        std::vector<size_t> m_members;
    };
    std::map<std::set<uint32_t>, size_t> groupIdx;
    std::vector<SinkGroup> groups;
    std::unordered_map<AstStmtExpr*, const std::set<uint32_t>*> narrowedStmt;
    std::unordered_set<AstIf*> modifiedIfs;
    size_t totalDeferred = 0;
    size_t totalDroppedTrigs = 0;

    for (size_t idx = 0; idx < entries.size(); ++idx) {
        const NbaEntry& e = entries[idx];
        if (e.m_pinned || e.m_sinks.empty()) continue;
        auto it = groupIdx.find(e.m_sinks);
        if (it == groupIdx.end()) {
            const size_t gid = groups.size();
            groupIdx.emplace(e.m_sinks, gid);
            SinkGroup g;
            g.m_keep = e.m_sinks;
            groups.push_back(std::move(g));
            it = groupIdx.find(e.m_sinks);
        }
        SinkGroup& g = groups[it->second];
        g.m_members.push_back(idx);
        for (const uint32_t t : e.m_triggers) {
            if (!g.m_keep.count(t)) {
                g.m_dropped.insert(t);
                ++totalDroppedTrigs;
            }
        }
        narrowedStmt[e.m_stmtp] = &e.m_sinks;
        modifiedIfs.insert(e.m_ifp);
        ++totalDeferred;
    }

    if (groups.empty()) return;

    // 6. Rewrite modified AstIf blocks in _eval_nba, preserving exact order.
    for (AstIf* const ifp : modifiedIfs) {
        std::vector<AstNode*> body;
        for (AstNode* sp = ifp->thensp(); sp; sp = sp->nextp()) body.push_back(sp);
        std::vector<std::pair<const std::set<uint32_t>*, std::vector<AstNode*>>> runs;
        for (AstNode* const sp : body) {
            const std::set<uint32_t>* key = nullptr;
            if (AstStmtExpr* const sep = VN_CAST(sp, StmtExpr)) {
                const auto it = narrowedStmt.find(sep);
                if (it != narrowedStmt.end()) key = it->second;
            }
            if (runs.empty() || runs.back().first != key) {
                runs.emplace_back(key, std::vector<AstNode*>{sp});
            } else {
                runs.back().second.push_back(sp);
            }
        }
        if (runs.size() == 1 && runs[0].first != nullptr) {
            AstNodeExpr* const newCondp
                = buildTriggerCond(ifp->fileline(), nbaTrigVscp, *runs[0].first);
            ifp->condp()->replaceWith(newCondp);
            continue;
        }
        AstNode* replacementp = nullptr;
        for (auto& run : runs) {
            AstNodeExpr* const condp
                = run.first ? buildTriggerCond(ifp->fileline(), nbaTrigVscp, *run.first)
                            : ifp->condp()->cloneTree(false);
            AstIf* const newIfp = new AstIf{ifp->fileline(), condp};
            for (AstNode* const sp : run.second) {
                sp->unlinkFrBack();
                newIfp->addThensp(sp);
            }
            addList(replacementp, newIfp);
        }
        ifp->replaceWith(replacementp);
        VL_DO_DANGLING(ifp->deleteTree(), ifp);
    }

    // 7. Emit per-group dirty flag, cold pre-NBA refresh function, and _eval hooks.
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    FileLine* const topFlp = netlistp->fileline();

    for (size_t gid = 0; gid < groups.size(); ++gid) {
        const SinkGroup& g = groups[gid];
        AstVarScope* const dirtyp
            = scopeTopp->createTemp("__Vclkskip_sink_d" + cvtToStr(gid), 1);
        dirtyp->trace(false);
        dirtyp->varp()->trace(false);
        dirtyp->varp()->noSubst(true);
        staticInitp->addInitsp(new AstAssign{topFlp, new AstVarRef{topFlp, dirtyp, VAccess::WRITE},
                                             new AstConst{topFlp, AstConst::BitFalse{}}});

        AstCFunc* const refreshp
            = new AstCFunc{topFlp, "_clkskip_sink_refresh__" + cvtToStr(gid), scopeTopp, ""};
        refreshp->dontCombine(true);
        refreshp->isStatic(false);
        refreshp->isLoose(true);
        refreshp->slow(true);  // Cold path: only runs on wake edges after sleep
        refreshp->isConst(false);
        refreshp->declPrivate(true);
        scopeTopp->addBlocksp(refreshp);
        for (const size_t idx : g.m_members) {
            AstCCall* const cp = new AstCCall{topFlp, entries[idx].m_calleep};
            cp->dtypeSetVoid();
            refreshp->addStmtsp(cp->makeStmt());
        }
        refreshp->addStmtsp(new AstAssign{topFlp, new AstVarRef{topFlp, dirtyp, VAccess::WRITE},
                                          new AstConst{topFlp, AstConst::BitFalse{}}});

        // Pre-NBA refresh: if (VL_UNLIKELY(dirtyp && triggered(K))) refresh();
        AstNodeExpr* const wakeCondp = new AstLogAnd{
            topFlp, new AstVarRef{topFlp, dirtyp, VAccess::READ},
            buildTriggerCond(topFlp, nbaTrigVscp, g.m_keep)};
        AstCCall* const refCallp = new AstCCall{topFlp, refreshp};
        refCallp->dtypeSetVoid();
        AstIf* const preIfp = new AstIf{topFlp, wakeCondp, refCallp->makeStmt()};
        preIfp->branchPred(VBranchPred::BP_UNLIKELY);
        nbaCallStmtp->addHereThisAsNext(preIfp);

        // Post-NBA dirty mark: if (!triggered(K) && triggered(D)) dirtyp = 1;
        AstNodeExpr* const sleepCondp = new AstLogAnd{
            topFlp, new AstLogNot{topFlp, buildTriggerCond(topFlp, nbaTrigVscp, g.m_keep)},
            buildTriggerCond(topFlp, nbaTrigVscp, g.m_dropped)};
        AstIf* const postIfp = new AstIf{
            topFlp, sleepCondp,
            new AstAssign{topFlp, new AstVarRef{topFlp, dirtyp, VAccess::WRITE},
                          new AstConst{topFlp, AstConst::BitTrue{}}}};
        nbaCallStmtp->addNextHere(postIfp);
    }

    V3Stats::addStat("Optimizations, Clock skip sink groups", groups.size());
    V3Stats::addStat("Optimizations, Clock skip sink deferred calls", totalDeferred);
    V3Stats::addStat("Optimizations, Clock skip sink triggers dropped", totalDroppedTrigs);
    V3Global::dumpCheckGlobalTree("clkskipsink", 0, dumpTree() >= 3);
}
