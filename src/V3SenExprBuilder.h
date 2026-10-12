// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Builder for sensitivity checking expressions.
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

#ifndef VERILATOR_V3SENEXPRBUILDER_H_
#define VERILATOR_V3SENEXPRBUILDER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

//######################################################################
// SenExprBuilder constructs the expressions used to compute if an
// AstSenTree have triggered

class SenExprBuilder final {
    // STATE
    AstScope* const m_scopep;  // The scope

    std::vector<AstVar*> m_locals;  // Trigger eval local variables
    std::vector<AstNodeStmt*> m_inits;  // Initialization statements for previous values
    std::vector<AstNodeStmt*> m_preUpdates;  // Pre update assignments
    std::vector<AstNodeStmt*> m_postUpdates;  // Post update assignments

    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_prev;  // The 'previous value' signals
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_curr;  // The 'current value' signals
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_changed;  // The 'value changed' flags of
                                                                 // wide change-detected signals
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_dirtyPrev;  // Previous value for a dirty
                                                                   // hybrid sensitivity
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_dirtyChg;  // Compare result for that
                                                                  // sensitivity
    std::unordered_set<VNRef<AstNode>> m_hasPreUpdate;  // Whether the given sen expression already
                                                        // has an update statement in m_preUpdates
    std::unordered_set<VNRef<AstNode>> m_hasPostUpdate;  // Likewise for m_postUpdates

    V3UniqueNames m_currNames{"__Vtrigcurrexpr"};  // For generating unique current value
                                                   // signal names
    V3UniqueNames m_prevNames{"__Vtrigprevexpr"};  // Likewise for previous values
    V3UniqueNames m_chgNames{"__Vtrigchgexpr"};  // Likewise for 'changed' flags
    int m_dirtySeq = 0;  // Unique suffix for dirty-bit state variables

    // Wide packed signals under change detection: compare once into a flag, and copy
    // the previous value only when the flag is set. The unconditional copy was a full
    // copy of the signal (hundreds of words for struct arrays) on every trigger
    // evaluation, of which there are several per clock.
    static bool useChangedFlag(const AstNodeExpr* exprp) {
        return exprp->isWide() && !VN_IS(exprp->dtypep()->skipRefp(), UnpackArrayDType);
    }

    static bool isSupportedDType(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (VN_IS(dtypep, BasicDType)) return true;
        if (VN_IS(dtypep, PackArrayDType)) return true;
        if (VN_IS(dtypep, UnpackArrayDType)) return isSupportedDType(dtypep->subDTypep());
        if (VN_IS(dtypep, NodeUOrStructDType)) return true;  // All are packed at the moment
        return false;
    }

    static bool isSimpleExpr(const AstNode* const exprp) {
        return exprp->forall([](const AstNode* const nodep) {
            return VN_IS(nodep, Const) || VN_IS(nodep, NodeVarRef) || VN_IS(nodep, Sel)
                   || VN_IS(nodep, NodeSel) || VN_IS(nodep, MemberSel)
                   || VN_IS(nodep, CMethodHard);
        });
    }

    // METHODS
    AstNodeExpr* getCurr(AstNodeExpr* exprp) {
        // For simple expressions like varrefs or selects, just use them directly
        if (isSimpleExpr(exprp)) return exprp->cloneTree(false);

        // Create the 'current value' variable
        FileLine* const flp = exprp->fileline();
        auto result = m_curr.emplace(*exprp, nullptr);
        if (result.second) {
            AstVar* const varp
                = new AstVar{flp, VVarType::BLOCKTEMP, m_currNames.get(exprp), exprp->dtypep()};
            varp->funcLocal(true);
            m_locals.push_back(varp);
            AstVarScope* vscp = new AstVarScope{flp, m_scopep, varp};
            m_scopep->addVarsp(vscp);
            result.first->second = vscp;
        }
        AstVarScope* const currp = result.first->second;

        // Add pre update if it does not exist yet in this round
        if (m_hasPreUpdate.emplace(*currp).second) {
            m_preUpdates.push_back(new AstAssign{flp, new AstVarRef{flp, currp, VAccess::WRITE},
                                                 exprp->cloneTree(false)});
        }
        return new AstVarRef{flp, currp, VAccess::READ};
    }
    AstVarScope* getPrev(AstNodeExpr* exprp) {
        FileLine* const flp = exprp->fileline();
        const auto rdCurr = [=]() { return getCurr(exprp); };

        // Create the 'previous value' variable
        auto it = m_prev.find(*exprp);
        if (it == m_prev.end()) {
            // For readability, use the scoped signal name if the trigger is a simple AstVarRef
            string name;
            if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
                AstVarScope* vscp = refp->varScopep();
                name = "__Vtrigrprev__" + vscp->scopep()->nameDotless() + "__"
                       + vscp->varp()->name();
            } else {
                name = m_prevNames.get(exprp);
            }

            AstVarScope* prevp;
            if (m_scopep->isTop()) {
                prevp = m_scopep->createTemp(name, exprp->dtypep());
            } else {
                AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP, m_prevNames.get(exprp),
                                                exprp->dtypep()};
                varp->funcLocal(true);
                m_locals.push_back(varp);
                prevp = new AstVarScope{flp, m_scopep, varp};
                m_scopep->addVarsp(prevp);
            }
            it = m_prev.emplace(*exprp, prevp).first;

            // Add the initializer init
            AstAssign* const initp = new AstAssign{flp, new AstVarRef{flp, prevp, VAccess::WRITE},
                                                   exprp->cloneTree(false)};
            m_inits.push_back(initp);
        }

        AstVarScope* const prevp = it->second;

        const auto wrPrev = [=]() { return new AstVarRef{flp, prevp, VAccess::WRITE}; };

        // Add post update if it does not exist yet
        if (m_hasPostUpdate.emplace(*exprp).second) {
            if (!isSupportedDType(exprp->dtypep())) {
                exprp->v3warn(E_UNSUPPORTED,
                              "Unsupported: Cannot detect changes on expression of complex type"
                              " (see combinational cycles reported by UNOPTFLAT)");
                return prevp;
            }

            if (AstUnpackArrayDType* const dtypep = VN_CAST(exprp->dtypep(), UnpackArrayDType)) {
                AstCMethodHard* const cmhp = new AstCMethodHard{flp, wrPrev(), "assign", rdCurr()};
                cmhp->dtypeSetVoid();
                m_postUpdates.push_back(cmhp->makeStmt());
            } else if (useChangedFlag(exprp)) {
                // Copy only when the value changed (the flag is computed in the pre updates)
                AstVarScope* const chgp = getChanged(exprp, prevp);
                AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, chgp, VAccess::READ}};
                ifp->addThensp(new AstAssign{flp, wrPrev(), rdCurr()});
                m_postUpdates.push_back(ifp);
            } else {
                m_postUpdates.push_back(new AstAssign{flp, wrPrev(), rdCurr()});
            }
        }

        return prevp;
    }
    // The 'changed' flag of a wide change-detected expression, assigned 'curr != prev' in
    // the pre updates (before any trigger is computed and before any previous value is
    // updated). One builder serves every trigger function ('stl', 'act', 'nba', ...), so
    // the flag is a module-level temporary at the top scope (like the 'previous value'
    // variables) and EVERY trigger function that uses it recomputes it in its own pre
    // updates -- the per-round m_hasPreUpdate set (cleared by getAndClearPreUpdates)
    // tracks that, exactly as for the 'current value' temporaries.
    AstVarScope* getChanged(AstNodeExpr* exprp, AstVarScope* prevp) {
        FileLine* const flp = exprp->fileline();
        auto it = m_changed.find(*exprp);
        if (it == m_changed.end()) {
            AstVarScope* chgp;
            if (m_scopep->isTop()) {
                chgp = m_scopep->createTemp(m_chgNames.get(exprp), 1);
            } else {
                AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP,
                                                m_chgNames.get(exprp), VFlagBitPacked{}, 1};
                varp->funcLocal(true);
                m_locals.push_back(varp);
                chgp = new AstVarScope{flp, m_scopep, varp};
                m_scopep->addVarsp(chgp);
            }
            it = m_changed.emplace(*exprp, chgp).first;
        }
        AstVarScope* const chgp = it->second;
        // Add the compare to this round's pre updates if not there yet
        if (m_hasPreUpdate.emplace(*chgp).second) {
            AstNeq* const neqp
                = new AstNeq{flp, getCurr(exprp), new AstVarRef{flp, prevp, VAccess::READ}};
            m_preUpdates.push_back(
                new AstAssign{flp, new AstVarRef{flp, chgp, VAccess::WRITE}, neqp});
        }
        return chgp;
    }

    // Wide hybrid cuts compare one dirty bit per 32-bit word instead of the
    // vector. The bit is a level, sampled into the trigger vector before the
    // post-update clears it. It is not itself change-detected: clearing it
    // would otherwise schedule a second pass. Returns null when this
    // sensitivity must keep the value compare (a primary input, a public or
    // forced or DPI-written signal, a narrow value, an unpacked array).
    AstNodeExpr* dirtyTerm(AstNodeExpr* senp) {
        if (!v3Global.opt.fDirty()) return nullptr;
        AstVarScope* vscp = nullptr;
        int lsb = 0;
        int width = 0;
        if (AstVarRef* const refp = VN_CAST(senp, VarRef)) {
            vscp = refp->varScopep();
            lsb = 0;
            width = refp->varp()->width();
        } else if (AstSel* const selp = VN_CAST(senp, Sel)) {
            AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef);
            if (!refp || !VN_IS(selp->lsbp(), Const) || !VN_IS(selp->widthp(), Const)) {
                return nullptr;
            }
            vscp = refp->varScopep();
            lsb = selp->lsbConst();
            width = selp->widthConst();
        } else {
            return nullptr;
        }
        if (!vscp || width <= 0) return nullptr;
        AstVar* const varp = vscp->varp();
        if (varp->width() <= VL_QUADSIZE) return nullptr;
        AstNodeDType* const dtypep = varp->dtypep() ? varp->dtypep()->skipRefp() : nullptr;
        if (!dtypep || !dtypep->isIntegralOrPacked()) return nullptr;
        if (VN_IS(dtypep, UnpackArrayDType)) return nullptr;
        // A store the generated model does not perform would never set the
        // bit. Those signals keep the value compare.
        if (varp->isSigPublic() || varp->isForceable() || varp->isWrittenByDpi()) return nullptr;
        if (varp->isPrimaryInish() || varp->isWrittenBySuspendable()) return nullptr;
        if (varp->direction() == VDirection::INOUT) return nullptr;

        FileLine* const flp = senp->fileline();
        if (!vscp->dirtyWordsp()) {
            const int nWords = (varp->width() + 31) / 32;
            string base = vscp->name();
            for (char& c : base) {
                const unsigned char u = static_cast<unsigned char>(c);
                const bool ok = (u >= '0' && u <= '9') || (u >= 'A' && u <= 'Z')
                                || (u >= 'a' && u <= 'z');
                if (!ok) c = '_';
            }
            base += "_" + cvtToStr(++m_dirtySeq);
            AstVarScope* const wordsp = m_scopep->createTemp("__Vdirtyw_" + base, nWords);
            AstVarScope* const allp = m_scopep->createTemp("__Vdirtya_" + base, 1);
            for (AstVarScope* const createdp : {wordsp, allp}) {
                createdp->trace(false);
                createdp->varp()->trace(false);
                createdp->varp()->noSubst(true);
            }
            vscp->dirtyWordsp(wordsp);
            vscp->dirtyAllp(allp);
            V3Stats::addStat("Optimizations, Dirty-bit signals", 1);
        }

        AstVarScope* const wordsp = vscp->dirtyWordsp();
        AstVarScope* const allp = vscp->dirtyAllp();
        const int nWords = wordsp->width();
        int w0 = lsb >> 5;
        int w1 = (lsb + width - 1) >> 5;
        if (w0 < 0) w0 = 0;
        if (w1 >= nWords) w1 = nWords - 1;
        if (w1 < w0) w1 = w0;
        const auto dirtyLevel = [&]() {
            AstSel* const bitselp = new AstSel{flp, new AstVarRef{flp, wordsp, VAccess::READ}, w0,
                                                w1 - w0 + 1};
            return new AstLogOr{flp, new AstVarRef{flp, allp, VAccess::READ},
                                new AstRedOr{flp, bitselp}};
        };

        // A store sets the bit even when a later store in the same pass puts
        // the old value back. The trigger still compares, but only if a bit
        // is set, and it compares the value after the whole pass. A stable
        // value does not schedule another pass. No store means no compare.
        auto prevIt = m_dirtyPrev.find(*senp);
        if (prevIt == m_dirtyPrev.end()) {
            const string base = "__Vdirtyprev_" + cvtToStr(++m_dirtySeq);
            AstVarScope* const createdp = m_scopep->createTemp(base, senp->dtypep());
            createdp->trace(false);
            createdp->varp()->trace(false);
            createdp->varp()->noSubst(true);
            prevIt = m_dirtyPrev.emplace(*senp, createdp).first;
        }
        auto chgIt = m_dirtyChg.find(*senp);
        if (chgIt == m_dirtyChg.end()) {
            const string base = "__Vdirtychg_" + cvtToStr(++m_dirtySeq);
            AstVarScope* const createdp = m_scopep->createTemp(base, 1);
            createdp->trace(false);
            createdp->varp()->trace(false);
            createdp->varp()->noSubst(true);
            chgIt = m_dirtyChg.emplace(*senp, createdp).first;
        }
        AstVarScope* const prevp = prevIt->second;
        AstVarScope* const chgp = chgIt->second;

        if (m_hasPreUpdate.emplace(*chgp).second) {
            AstNeq* const neqp = new AstNeq{flp, senp->cloneTree(false),
                                            new AstVarRef{flp, prevp, VAccess::READ}};
            AstAssign* const setp
                = new AstAssign{flp, new AstVarRef{flp, chgp, VAccess::WRITE}, neqp};
            AstAssign* const clrp = new AstAssign{flp, new AstVarRef{flp, chgp, VAccess::WRITE},
                                                  new AstConst{flp, AstConst::BitTrue{}, false}};
            m_preUpdates.push_back(new AstIf{flp, dirtyLevel(), setp, clrp});
        }
        if (m_hasPostUpdate.emplace(*chgp).second) {
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, chgp, VAccess::READ}};
            ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, prevp, VAccess::WRITE},
                                         senp->cloneTree(false)});
            m_postUpdates.push_back(ifp);
        }
        // Clear after the trigger bit has been sampled. Settle, input-combo,
        // and active each get their own clear. The dirty bit is not itself
        // change-detected, so the 1-to-0 clear does not schedule a pass.
        if (m_hasPostUpdate.emplace(*wordsp).second) {
            AstConst* const zerop = new AstConst{flp, AstConst::DTyped{}, wordsp->dtypep()};
            m_postUpdates.push_back(new AstAssign{
                flp, new AstVarRef{flp, wordsp, VAccess::WRITE}, zerop});
            m_postUpdates.push_back(new AstAssign{
                flp, new AstVarRef{flp, allp, VAccess::WRITE},
                new AstConst{flp, AstConst::BitTrue{}, false}});
        }
        return new AstVarRef{flp, chgp, VAccess::READ};
    }

    std::pair<AstNodeExpr*, bool> createTerm(AstSenItem* senItemp) {
        FileLine* const flp = senItemp->fileline();
        AstNodeExpr* const senp = senItemp->sensp();

        const auto currp = [=]() { return getCurr(senp); };
        const auto prevp = [=]() { return new AstVarRef{flp, getPrev(senp), VAccess::READ}; };
        const auto lsb = [=](AstNodeExpr* opp) { return new AstSel{flp, opp, 0, 1}; };

        // All event signals should be 1-bit at this point
        switch (senItemp->edgeType()) {
        case VEdgeType::ET_ILLEGAL:
            return {nullptr, false};  // We already warn for this in V3LinkResolve
        case VEdgeType::ET_CHANGED:
        case VEdgeType::ET_HYBRID:  //
            if (senItemp->edgeType() == VEdgeType::ET_HYBRID) {
                if (AstNodeExpr* const dirtyp = dirtyTerm(senp)) return {dirtyp, true};
            }
            if (VN_IS(senp->dtypep(), UnpackArrayDType)) {
                AstCMethodHard* const resultp = new AstCMethodHard{flp, currp(), "neq", prevp()};
                resultp->dtypeSetBit();
                return {resultp, true};
            }
            if (useChangedFlag(senp)) {
                // One compare per evaluation, shared with the conditional previous-value copy
                AstVarScope* const prevVscp = getPrev(senp);
                AstVarScope* const chgp = getChanged(senp, prevVscp);
                return {new AstVarRef{flp, chgp, VAccess::READ}, true};
            }
            return {new AstNeq{flp, currp(), prevp()}, true};
        case VEdgeType::ET_BOTHEDGE:  //
            return {lsb(new AstXor{flp, currp(), prevp()}), false};
        case VEdgeType::ET_POSEDGE:  //
            return {lsb(new AstAnd{flp, currp(), new AstNot{flp, prevp()}}), false};
        case VEdgeType::ET_NEGEDGE:  //
            return {lsb(new AstAnd{flp, new AstNot{flp, currp()}, prevp()}), false};
        case VEdgeType::ET_EVENT: {
            UASSERT_OBJ(v3Global.hasEvents(), senItemp, "Inconsistent");
            {
                // If the event is fired, set up the clearing process
                AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
                callp->dtypeSetBit();
                AstIf* const ifp = new AstIf{flp, callp};
                m_postUpdates.push_back(ifp);

                // Clear 'fired' state when done
                AstCMethodHard* const clearp = new AstCMethodHard{flp, currp(), "clearFired"};
                clearp->dtypeSetVoid();
                ifp->addThensp(clearp->makeStmt());

                // Enqueue for clearing 'triggered' state on next eval
                AstTextBlock* const blockp = new AstTextBlock{flp};
                ifp->addThensp(blockp);
                const auto add = [&](const string& text) { blockp->addText(flp, text, true); };
                add("vlSymsp->enqueueTriggeredEventForClearing(");
                blockp->addNodesp(currp());
                add(");\n");
            }

            // Get 'fired' state
            AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
            callp->dtypeSetBit();
            return {callp, false};
        }
        case VEdgeType::ET_TRUE:  //
            return {currp(), false};
        default:  // LCOV_EXCL_START
            senItemp->v3fatalSrc("Unknown edge type");
            return {nullptr, false};
        }  // LCOV_EXCL_STOP
    }

public:
    // Returns the expression computing the trigger, and a bool indicating that
    // this trigger should be fired on the first evaluation (at initialization)
    std::pair<AstNodeExpr*, bool> build(const AstSenTree* senTreep) {
        FileLine* const flp = senTreep->fileline();
        AstNodeExpr* resultp = nullptr;
        bool firedAtInitialization = false;
        for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
             senItemp = VN_AS(senItemp->nextp(), SenItem)) {
            const auto& pair = createTerm(senItemp);
            if (AstNodeExpr* const termp = pair.first) {
                resultp = resultp ? new AstOr{flp, resultp, termp} : termp;
                firedAtInitialization |= pair.second;
            }
        }
        return {resultp, firedAtInitialization};
    }

    std::vector<AstNodeStmt*> getAndClearInits() { return std::move(m_inits); }
    std::vector<AstVar*> getAndClearLocals() { return std::move(m_locals); }

    std::vector<AstNodeStmt*> getAndClearPreUpdates() {
        m_hasPreUpdate.clear();
        return std::move(m_preUpdates);
    }

    std::vector<AstNodeStmt*> getAndClearPostUpdates() {
        m_hasPostUpdate.clear();
        return std::move(m_postUpdates);
    }

    // CONSTRUCTOR
    explicit SenExprBuilder(AstScope* scopep)
        : m_scopep{scopep} {}
};

#endif  // Guard
