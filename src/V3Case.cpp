// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break case statements up and add Unknown assigns
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
// V3Case's Transformations:
//
// Each module:
//      TBD: Eliminate tristates by adding __in, __inen, __en wires in parallel
//          Need __en in changed list if a signal is on the LHS of a assign
//      Cases:
//          CASE(v) CASEITEM(items,body) ->  IF (OR (EQ (AND v mask)
//                                                      (AND item1 mask))
//                                                  (other items))
//                                              body
//              Or, converts to a if/else tree.
//      FUTURES:
//          Large 16+ bit tables with constants and no masking (address muxes)
//              Enter all into std::multimap, sort by value and use a tree of < and == compares.
//          "Diagonal" find of {rightmost,leftmost} bit {set,clear}
//              Ignoring mask, check each value is unique (using std::multimap as above?)
//              Each branch is then mask-and-compare operation (IE
//              <000000001_000000000 at midpoint.)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Case.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

#define CASE_OVERLAP_WIDTH 16  // Maximum width we can check for overlaps in
#define CASE_BARF 999999  // Magic width when non-constant
#define CASE_ENCODER_GROUP_DEPTH 8  // Levels of priority to be ORed together in top IF tree

//######################################################################

class CaseLintVisitor final : public VNVisitor {
private:
    const AstNodeCase* m_caseExprp
        = nullptr;  // Under a CASE value node, if so the relevant case statement

    // METHODS

    void visit(AstNodeCase* nodep) override {
        if (VN_IS(nodep, Case) && VN_AS(nodep, Case)->casex()) {
            nodep->v3warn(CASEX, "Suggest casez (with ?'s) in place of casex (with X's)");
        }
        // Detect multiple defaults
        bool hitDefault = false;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                if (hitDefault) {
                    itemp->v3error("Multiple default statements in case statement.");
                }
                hitDefault = true;
            }
        }

        // Check for X/Z in non-casex statements
        {
            m_caseExprp = nodep;
            iterate(nodep->exprp());
            for (AstCaseItem* itemp = nodep->itemsp(); itemp;
                 itemp = VN_AS(itemp->nextp(), CaseItem)) {
                iterateAndNextNull(itemp->condsp());
            }
            m_caseExprp = nullptr;
        }
    }
    void visit(AstConst* nodep) override {
        // See also neverItem
        if (m_caseExprp && nodep->num().isFourState()) {
            if (VN_IS(m_caseExprp, GenCase)) {
                nodep->v3error("Use of x/? constant in generate case statement, "
                               "(no such thing as 'generate casez')");
            } else if (VN_IS(m_caseExprp, Case) && VN_AS(m_caseExprp, Case)->casex()) {
                // Don't sweat it, we already complained about casex in general
            } else if (VN_IS(m_caseExprp, Case)
                       && (VN_AS(m_caseExprp, Case)->casez()
                           || VN_AS(m_caseExprp, Case)->caseInside())) {
                if (nodep->num().isAnyX()) {
                    nodep->v3warn(CASEWITHX, "Use of x constant in casez statement, "
                                             "(perhaps intended ?/z in constant)");
                }
            } else {
                nodep->v3warn(CASEWITHX, "Use of x/? constant in case statement, "
                                         "(perhaps intended casex/casez)");
            }
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CaseLintVisitor(AstNodeCase* nodep) { iterate(nodep); }
    ~CaseLintVisitor() override = default;
};

//######################################################################
// Case-to-table lowering
//
// A case whose index expression is narrow and whose every arm produces the
// same kind of constant result is a read-only lookup. Lower it to one
// AstConstPool table (deduplicated across the whole design by
// AstConstPool::findTable) plus a single AstArraySel, instead of the
// compare tree replaceCaseFast/replaceCaseComplicated would build -- and
// instead of that tree being cloned into every V3Task inline site.
//
// Recognized arm shapes (exactly one effective statement per arm):
//   - <lhs> = const          blocking or nonblocking, same lhs on every arm
//   - return const           inside a function; kept as 'return TABLE[idx]'
// A default arm supplies the value for every uncovered index; without one
// the arms must provably cover all 2^indexWidth patterns.

static constexpr int kCaseTableMaxIndexWidth = 12;  // 4096 entries max
static constexpr int kCaseTableMaxValueWidth = 32;
static constexpr int kCaseTableMinArms = 8;  // distinct index values

// Const node only -- no cast peeling. A constant hidden under a cast has
// already been folded by V3Const; anything else is left to the tree path.
static AstConst* caseTableConst(AstNodeExpr* nodep) {
    return VN_CAST(nodep, Const);
}

static bool caseTablePlainConst(AstConst* constp) {
    return constp && !constp->num().isFourState() && !constp->num().isDouble()
           && !constp->num().isString();
}

//######################################################################
// Case state, as a visitor of each AstNode

class CaseVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared each Case
    //  AstIf::user3()          -> bool.  Set true to indicate clone not needed
    const VNUser3InUse m_inuser3;

    // STATE
    VDouble0 m_statCaseFast;  // Statistic tracking
    VDouble0 m_statCaseSlow;  // Statistic tracking
    VDouble0 m_statCaseTable;  // Statistic tracking
    const AstNode* m_alwaysp = nullptr;  // Always in which case is located
    AstNodeFTask* m_ftaskp = nullptr;  // Function/task containing the case, if any

    // Per-CASE
    int m_caseWidth = 0;  // Width of valueItems
    int m_caseItems = 0;  // Number of caseItem unique values
    bool m_caseNoOverlapsAllCovered = false;  // Proven to be synopsys parallel_case compliant
    // For each possible value, the case branch we need
    std::array<AstNode*, 1 << CASE_OVERLAP_WIDTH> m_valueItem;

    // METHODS
    bool caseIsEnumComplete(AstCase* nodep, uint32_t numCases) {
        // Return true if case is across an enum, and every value in the case
        // statement corresponds to one of the enum values
        if (!nodep->uniquePragma() && !nodep->unique0Pragma()) return false;
        AstEnumDType* const enumDtp
            = VN_CAST(nodep->exprp()->dtypep()->skipRefToEnump(), EnumDType);
        if (!enumDtp) return false;  // Case isn't enum
        AstBasicDType* const basicp = enumDtp->subDTypep()->basicp();
        if (!basicp) return false;  // Not simple type (perhaps IEEE illegal)
        if (basicp->width() > 32) return false;
        // Find all case values into a set
        std::set<uint32_t> caseSet;
        for (uint32_t i = 0; i < numCases; ++i) {  // All case items
            if (m_valueItem[i]) caseSet.emplace(i);
        }
        // Find all enum values into a set
        std::set<uint32_t> enumSet;
        for (AstEnumItem* itemp = enumDtp->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            AstConst* const econstp = VN_AS(itemp->valuep(), Const);
            const uint32_t val = econstp->toUInt();
            // UINFO(9, "Complete enum item " << val << ": " << itemp << endl);
            enumSet.emplace(val);
        }
        // If sets match, all covered
        return (caseSet == enumSet);
    }
    bool isCaseTreeFast(AstCase* nodep) {
        int width = 0;
        bool opaque = false;
        m_caseItems = 0;
        m_caseNoOverlapsAllCovered = true;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode* icondp = itemp->condsp(); icondp; icondp = icondp->nextp()) {
                if (icondp->width() > width) width = icondp->width();
                if (icondp->isDouble()) opaque = true;
                if (!VN_IS(icondp, Const)) width = CASE_BARF;  // Can't parse; not a constant
                m_caseItems++;
            }
        }
        m_caseWidth = width;
        if (width == 0 || width > CASE_OVERLAP_WIDTH || opaque) {
            m_caseNoOverlapsAllCovered = false;
            return false;  // Too wide for analysis
        }
        UINFO(8, "Simple case statement: " << nodep << endl);
        const uint32_t numCases = 1UL << m_caseWidth;
        // Zero list of items for each value
        for (uint32_t i = 0; i < numCases; ++i) m_valueItem[i] = nullptr;
        // Now pick up the values for each assignment
        // We can cheat and use uint32_t's because we only support narrow case's
        bool reportedOverlap = false;
        bool reportedSubcase = false;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode* icondp = itemp->condsp(); icondp; icondp = icondp->nextp()) {
                // if (debug() >= 9) icondp->dumpTree("-  caseitem: ");
                AstConst* const iconstp = VN_AS(icondp, Const);
                UASSERT_OBJ(iconstp, nodep, "above 'can't parse' should have caught this");
                if (neverItem(nodep, iconstp)) {
                    // X in casez can't ever be executed
                } else {
                    V3Number nummask{itemp, iconstp->width()};
                    nummask.opBitsNonX(iconstp->num());
                    const uint32_t mask = nummask.toUInt();
                    V3Number numval{itemp, iconstp->width()};
                    numval.opBitsOne(iconstp->num());
                    const uint32_t val = numval.toUInt();

                    uint32_t firstOverlap = 0;
                    bool foundOverlap = false;
                    bool foundHit = false;
                    for (uint32_t i = 0; i < numCases; ++i) {
                        if ((i & mask) == val) {
                            if (!m_valueItem[i]) {
                                m_valueItem[i] = itemp;
                                foundHit = true;
                            } else if (!foundOverlap) {
                                firstOverlap = i;
                                foundOverlap = true;
                                m_caseNoOverlapsAllCovered = false;
                            }
                        }
                    }
                    if (!nodep->priorityPragma()) {
                        // If this case statement doesn't have the priority
                        // keyword, we want to warn on any overlap.
                        if (!reportedOverlap && foundOverlap) {
                            icondp->v3warn(CASEOVERLAP, "Case values overlap (example pattern 0x"
                                                            << std::hex << firstOverlap << ")");
                            reportedOverlap = true;
                        }
                    } else {
                        // If this is a priority case, we only want to complain
                        // if every possible value for this item is already hit
                        // by some other item. This is true if foundHit is
                        // false.
                        if (!reportedSubcase && !foundHit) {
                            icondp->v3warn(CASEOVERLAP,
                                           "Case item ignored: every matching value is covered "
                                           "by an earlier item");
                            reportedSubcase = true;
                        }
                    }
                }
            }
            // Defaults were moved to last in the caseitem list by V3LinkDot
            if (itemp->isDefault()) {  // Case statement's default... Fill the table
                for (uint32_t i = 0; i < numCases; ++i) {
                    if (!m_valueItem[i]) m_valueItem[i] = itemp;
                }
            }
        }
        if (!caseIsEnumComplete(nodep, numCases)) {
            for (uint32_t i = 0; i < numCases; ++i) {
                if (!m_valueItem[i]) {
                    nodep->v3warn(CASEINCOMPLETE, "Case values incompletely covered "
                                                  "(example pattern 0x"
                                                      << std::hex << i << ")");
                    m_caseNoOverlapsAllCovered = false;
                    return false;
                }
            }
        }

        if (m_caseItems <= 3
            // Avoid e.g. priority expanders from going crazy in expansion
            || (m_caseWidth >= 8 && (m_caseItems <= (m_caseWidth + 1)))) {
            return false;  // Not worth simplifying
        }

        // Convert valueItem from AstCaseItem* to the expression
        // Not done earlier, as we may now have a nullptr because it's just a ";" NOP branch
        for (uint32_t i = 0; i < numCases; ++i) {
            if (AstCaseItem* const itemp = VN_AS(m_valueItem[i], CaseItem)) {
                m_valueItem[i] = itemp->stmtsp();
            }
        }
        return true;  // All is fine
    }

    AstNode* replaceCaseFastRecurse(AstNodeExpr* cexprp, int msb, uint32_t upperValue) {
        if (msb < 0) {
            // There's no space for a IF.  We know upperValue is thus down to a specific
            // exact value, so just return the tree value
            // Note can't clone here, as we're going to check for equivalence above
            AstNode* const foundp = m_valueItem[upperValue];
            return foundp;
        } else {
            // Make left and right subtrees
            // cexpr[msb:lsb] == 1
            AstNode* tree0p = replaceCaseFastRecurse(cexprp, msb - 1, upperValue | 0);
            AstNode* tree1p = replaceCaseFastRecurse(
                cexprp, msb - 1, upperValue | (1UL << static_cast<uint32_t>(msb)));

            if (tree0p == tree1p) {
                // Same logic on both sides, so we can just return one of 'em
                return tree0p;
            }
            // We could have a "checkerboard" with A B A B, we can use the same IF on both edges
            bool same = true;
            for (uint32_t a = upperValue, b = (upperValue | (1UL << msb));
                 a < (upperValue | (1UL << msb)); a++, b++) {
                if (m_valueItem[a] != m_valueItem[b]) {
                    same = false;
                    break;
                }
            }
            if (same) {
                VL_DO_DANGLING(tree1p->deleteTree(), tree1p);
                return tree0p;
            }

            // Must have differing logic, so make a selection

            // Case expressions can't be linked twice, so clone them
            if (tree0p && !tree0p->user3()) tree0p = tree0p->cloneTree(true);
            if (tree1p && !tree1p->user3()) tree1p = tree1p->cloneTree(true);

            // Alternate scheme if we ever do multiple bits at a time:
            // V3Number nummask (cexprp, cexprp->width(), (1UL<<msb));
            // AstNode* and1p = new AstAnd(cexprp->fileline(), cexprp->cloneTree(false),
            //                            new AstConst(cexprp->fileline(), nummask));
            AstNodeExpr* const and1p
                = new AstSel{cexprp->fileline(), cexprp->cloneTree(false), msb, 1};
            AstNodeExpr* const eqp
                = new AstNeq{cexprp->fileline(), new AstConst{cexprp->fileline(), 0}, and1p};
            AstIf* const ifp = new AstIf{cexprp->fileline(), eqp, tree1p, tree0p};
            ifp->user3(1);  // So we don't bother to clone it
            return ifp;
        }
    }

    void replaceCaseFast(AstCase* nodep) {
        // CASEx(cexpr,....
        // ->  tree of IF(msb,  IF(msb-1, 11, 10)
        //                      IF(msb-1, 01, 00))
        AstNodeExpr* const cexprp = nodep->exprp()->unlinkFrBack();

        if (debug() >= 9) {  // LCOV_EXCL_START
            for (uint32_t i = 0; i < (1UL << m_caseWidth); ++i) {
                if (const AstNode* const itemp = m_valueItem[i]) {
                    UINFO(9, "Value " << std::hex << i << " " << itemp << endl);
                }
            }
        }  // LCOV_EXCL_STOP

        // Handle any assertions
        replaceCaseParallel(nodep, m_caseNoOverlapsAllCovered);

        AstNode::user3ClearTree();
        AstNode* ifrootp = replaceCaseFastRecurse(cexprp, m_caseWidth - 1, 0UL);
        // Case expressions can't be linked twice, so clone them
        if (ifrootp && !ifrootp->user3()) ifrootp = ifrootp->cloneTree(true);

        if (ifrootp) {
            nodep->replaceWith(ifrootp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        VL_DO_DANGLING(cexprp->deleteTree(), cexprp);
        if (debug() >= 9) ifrootp->dumpTree("-    _simp: ");
    }

    void replaceCaseComplicated(AstCase* nodep) {
        // CASEx(cexpr,ITEM(icond1,istmts1),ITEM(icond2,istmts2),ITEM(default,istmts3))
        // ->  IF((cexpr==icond1),istmts1,
        //                       IF((EQ (AND MASK cexpr) (AND MASK icond1)
        //                              ,istmts2, istmts3
        AstNodeExpr* const cexprp = nodep->exprp()->unlinkFrBack();
        // We'll do this in two stages.  First stage, convert the conditions to
        // the appropriate IF AND terms.
        if (debug() >= 9) nodep->dumpTree("-    _comp_IN::: ");
        bool hadDefault = false;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (!itemp->condsp()) {
                // Default clause.  Just make true, we'll optimize it away later
                itemp->addCondsp(new AstConst{itemp->fileline(), AstConst::BitTrue{}});
                hadDefault = true;
            } else {
                // Expressioned clause
                AstNodeExpr* icondNextp = nullptr;
                AstNodeExpr* ifexprp = nullptr;  // If expression to test
                for (AstNodeExpr* icondp = itemp->condsp(); icondp; icondp = icondNextp) {
                    icondNextp = VN_AS(icondp->nextp(), NodeExpr);
                    icondp->unlinkFrBack();

                    AstNodeExpr* condp = nullptr;  // Default is to use and1p/and2p
                    AstConst* const iconstp = VN_CAST(icondp, Const);
                    if (iconstp && neverItem(nodep, iconstp)) {
                        // X in casez can't ever be executed
                        VL_DO_DANGLING(icondp->deleteTree(), icondp);
                        VL_DANGLING(iconstp);
                        // For simplicity, make expression that is not equal, and let later
                        // optimizations remove it
                        condp = new AstConst{itemp->fileline(), AstConst::BitFalse{}};
                    } else if (AstInsideRange* const irangep = VN_CAST(icondp, InsideRange)) {
                        // Similar logic in V3Width::visit(AstInside)
                        condp = irangep->newAndFromInside(cexprp, irangep->lhsp()->unlinkFrBack(),
                                                          irangep->rhsp()->unlinkFrBack());
                    } else if (iconstp && iconstp->num().isFourState()
                               && (nodep->casex() || nodep->casez() || nodep->caseInside())) {
                        V3Number nummask{itemp, iconstp->width()};
                        nummask.opBitsNonX(iconstp->num());
                        V3Number numval{itemp, iconstp->width()};
                        numval.opBitsOne(iconstp->num());
                        AstNodeExpr* const and1p
                            = new AstAnd{itemp->fileline(), cexprp->cloneTree(false),
                                         new AstConst{itemp->fileline(), nummask}};
                        AstNodeExpr* const and2p = new AstAnd{
                            itemp->fileline(), new AstConst{itemp->fileline(), numval},
                            new AstConst{itemp->fileline(), nummask}};
                        VL_DO_DANGLING(icondp->deleteTree(), icondp);
                        VL_DANGLING(iconstp);
                        condp = AstEq::newTyped(itemp->fileline(), and1p, and2p);
                    } else {
                        // Not a caseX mask, we can build CASEEQ(cexpr icond)
                        AstNodeExpr* const and1p = cexprp->cloneTree(false);
                        AstNodeExpr* const and2p = icondp;
                        condp = AstEq::newTyped(itemp->fileline(), and1p, and2p);
                    }
                    if (!ifexprp) {
                        ifexprp = condp;
                    } else {
                        ifexprp = new AstLogOr{itemp->fileline(), ifexprp, condp};
                    }
                }
                // Replace expression in tree
                itemp->addCondsp(ifexprp);
            }
        }
        VL_DO_DANGLING(cexprp->deleteTree(), cexprp);
        if (!hadDefault) {
            // If there was no default, add a empty one, this greatly simplifies below code
            // and constant propagation will just eliminate it for us later.
            nodep->addItemsp(new AstCaseItem{
                nodep->fileline(), new AstConst{nodep->fileline(), AstConst::BitTrue{}}, nullptr});
        }
        if (debug() >= 9) nodep->dumpTree("-    _comp_COND: ");
        // Now build the IF statement tree
        // The tree can be quite huge.  Pull ever group of 8 out, and make a OR tree.
        // This reduces the depth for the bottom elements, at the cost of
        // some of the top elements.  If we ever have profiling data, we
        // should pull out the most common item from here and instead make
        // it the first IF branch.
        int depth = 0;
        AstNode* grouprootp = nullptr;
        AstIf* groupnextp = nullptr;
        AstIf* itemnextp = nullptr;
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            AstNode* const istmtsp = itemp->stmtsp();  // Maybe null -- no action.
            if (istmtsp) istmtsp->unlinkFrBackWithNext();
            // Expressioned clause
            AstNodeExpr* const ifexprp = itemp->condsp()->unlinkFrBack();
            {  // Prepare for next group
                if (++depth > CASE_ENCODER_GROUP_DEPTH) depth = 1;
                if (depth == 1) {  // First group or starting new group
                    itemnextp = nullptr;
                    AstIf* const newp = new AstIf{itemp->fileline(), ifexprp->cloneTree(true)};
                    if (groupnextp) {
                        groupnextp->addElsesp(newp);
                    } else {
                        grouprootp = newp;
                    }
                    groupnextp = newp;
                } else {  // Continue group, modify if condition to OR in this new condition
                    AstNodeExpr* const condp = groupnextp->condp()->unlinkFrBack();
                    groupnextp->condp(
                        new AstOr{ifexprp->fileline(), condp, ifexprp->cloneTree(true)});
                }
            }
            {  // Make the new lower IF and attach in the tree
                AstNodeExpr* itemexprp = ifexprp;
                VL_DANGLING(ifexprp);
                if (depth == CASE_ENCODER_GROUP_DEPTH) {  // End of group - can skip the condition
                    VL_DO_DANGLING(itemexprp->deleteTree(), itemexprp);
                    itemexprp = new AstConst{itemp->fileline(), AstConst::BitTrue{}};
                }
                AstIf* const newp = new AstIf{itemp->fileline(), itemexprp, istmtsp};
                if (itemnextp) {
                    itemnextp->addElsesp(newp);
                } else {
                    groupnextp->addThensp(newp);  // First in a new group
                }
                itemnextp = newp;
            }
        }
        if (debug() >= 9) nodep->dumpTree("-    _comp_TREE: ");
        // Handle any assertions
        replaceCaseParallel(nodep, false);
        // Replace the CASE... with IF...
        if (debug() >= 9 && grouprootp) grouprootp->dumpTree("-     _new: ");
        if (grouprootp) {
            nodep->replaceWith(grouprootp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void replaceCaseParallel(AstCase* nodep, bool noOverlapsAllCovered) {
        // Take the notParallelp tree under the case statement created by V3Assert
        // If the statement was proven to have no overlaps and all cases
        // covered, we're done with it.
        // Else, convert to a normal statement parallel with the case statement.
        if (nodep->notParallelp() && !noOverlapsAllCovered) {
            AstNode* const parp = nodep->notParallelp()->unlinkFrBackWithNext();
            nodep->addNextHere(parp);
        }
    }

    bool neverItem(AstCase* casep, AstConst* itemp) {
        // Xs in case or casez are impossible due to two state simulations
        if (casep->casex()) {
        } else if (casep->casez() || casep->caseInside()) {
            if (itemp->num().isAnyX()) return true;
        } else {
            if (itemp->num().isFourState()) return true;
        }
        return false;
    }

    // True when jumpGp targets a function-exit label: V3LinkJump places
    // 'return' labels in JumpBlocks nested directly under the function
    // body, while break/continue labels live under loop nodes. Walk the
    // label's block chain upward; only JumpBlock/JumpLabel nesting may
    // intervene before reaching the function.
    bool isFuncExitJump(const AstJumpGo* jumpGp, const AstNodeFTask* ftaskp) {
        const AstJumpLabel* const labelp = jumpGp->labelp();
        if (!labelp || !labelp->blockp()) return false;
        for (const AstNode* p = labelp->blockp(); p;) {
            if (p == ftaskp) return true;
            if (!VN_IS(p, JumpBlock) && !VN_IS(p, JumpLabel)) return false;
            // Ascend to the true parent: backp() of a mid-list node is the
            // previous sibling, so walk back to the list head first whose
            // backp() is the owning node.
            const AstNode* q = p;
            while (q->backp() && q->backp()->nextp() == q) q = q->backp();
            p = q->backp();
        }
        return false;
    }

    // Try to lower the case to a ConstPool lookup table. Returns true when
    // nodep was replaced (and deleted); the caller must not touch it then.
    bool tryCaseTable(AstCase* nodep) {
        if (nodep->casex() || nodep->casez() || nodep->caseInside()) return false;
        if (nodep->notParallelp()) return false;  // Keep the assertion block
        if (m_ftaskp && (m_ftaskp->dpiImport() || m_ftaskp->classMethod()
                         || m_ftaskp->recursive() || m_ftaskp->isConstructor())) {
            return false;  // Non-inlined bodies get their own CFunc emission
        }
        AstNodeExpr* const exprp = nodep->exprp();
        const int indexWidth = exprp ? exprp->width() : 0;
        if (indexWidth < 2 || indexWidth > kCaseTableMaxIndexWidth) return false;

        enum ArmKind : uint8_t { kNone, kAssign, kAssignDly, kReturn, kReturnGo };
        ArmKind kind = kNone;
        AstNodeExpr* lhsp = nullptr;  // Exemplar lhs for assign arms
        AstConst* defaultValp = nullptr;  // Default arm's value (in-tree)
        AstJumpGo* firstJumpGp = nullptr;  // Shared function-exit jump
        int valueWidth = 0;
        std::map<uint32_t, AstConst*> values;
        size_t nArms = 0;

        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            // One or two effective statements, through single-statement
            // begins. A trailing JumpGo is the lowered form of 'return
            // expr': V3LinkJump rewrites it to "assign the function return
            // variable; goto the function exit" long before this pass.
            AstNode* stmtp = itemp->stmtsp();
            AstNode* const outerp = stmtp;  // Node whose nextp is the 2nd stmt
            while (AstBegin* const begp = VN_CAST(stmtp, Begin)) {
                if (!begp->stmtsp() || begp->stmtsp()->nextp()) return false;
                stmtp = begp->stmtsp();
            }
            if (!stmtp) return false;
            AstNode* const secondp = outerp->nextp();
            AstJumpGo* const jumpGp = VN_CAST(secondp, JumpGo);
            if (secondp && !jumpGp) return false;
            if (jumpGp && jumpGp->nextp()) return false;

            AstConst* valp = nullptr;
            AstNodeExpr* thisLhs = nullptr;
            ArmKind thisKind = kNone;
            if (AstAssign* const assignp = VN_CAST(stmtp, Assign)) {
                thisKind = kAssign;
                thisLhs = assignp->lhsp();
                valp = caseTableConst(assignp->rhsp());
            } else if (AstAssignDly* const assignp = VN_CAST(stmtp, AssignDly)) {
                thisKind = kAssignDly;
                thisLhs = assignp->lhsp();
                valp = caseTableConst(assignp->rhsp());
            } else if (AstReturn* const retp = VN_CAST(stmtp, Return)) {
                thisKind = kReturn;
                if (retp->lhsp()) valp = caseTableConst(retp->lhsp());
            } else {
                return false;
            }
            if (jumpGp) {
                // 'return expr' shape: blocking assign to the function
                // return variable, then a jump to the function exit.
                // V3LinkJump wraps the whole body per return, so each arm
                // may target a different AstJumpLabel -- but every label
                // sits at the end of a singly-nested JumpBlock chain that
                // converges on the function epilogue, so they are all
                // semantically the same exit. Any one of them works.
                if (thisKind != kAssign || !m_ftaskp || !m_ftaskp->isFunction()) {
                    return false;
                }
                const AstVar* const fvarp = VN_CAST(m_ftaskp->fvarp(), Var);
                const AstVarRef* const lhsRefp = VN_CAST(thisLhs, VarRef);
                if (!fvarp || !lhsRefp || lhsRefp->varp() != fvarp) return false;
                if (!isFuncExitJump(jumpGp, m_ftaskp)) return false;
                if (!firstJumpGp) firstJumpGp = jumpGp;
                thisKind = kReturnGo;
            }
            if (!caseTablePlainConst(valp)) return false;
            if (valueWidth == 0) {
                valueWidth = valp->width();
            } else if (valp->width() != valueWidth) {
                return false;
            }
            if (kind == kNone) {
                kind = thisKind;
                lhsp = thisLhs;
            } else if (thisKind != kind) {
                return false;
            }
            if (thisLhs && lhsp && !thisLhs->sameTree(lhsp)) return false;
            if (thisLhs && !lhsp) return false;
            ++nArms;

            if (itemp->isDefault()) {
                if (defaultValp) return false;
                defaultValp = valp;
                continue;
            }
            bool anyLabel = false;
            for (AstNode* condp = itemp->condsp(); condp; condp = condp->nextp()) {
                AstNodeExpr* const cexprp = VN_CAST(condp, NodeExpr);
                AstConst* const labelp = cexprp ? caseTableConst(cexprp) : nullptr;
                if (!caseTablePlainConst(labelp) || labelp->width() != indexWidth) {
                    return false;
                }
                if (!values.emplace(labelp->toUInt(), valp).second) {
                    return false;  // Duplicate label: keep overlap lint
                }
                anyLabel = true;
            }
            if (!anyLabel) return false;  // Non-default item with no labels
        }
        if (kind == kNone || nArms == 0 || values.size() < kCaseTableMinArms) return false;
        const uint32_t tableSize = 1u << indexWidth;
        if (!defaultValp && values.size() != tableSize) return false;

        // The table element must be exactly the assignment/return target
        // width: a narrower element would be zero-extended where the
        // original constant might have been sign-extended.
        int targetWidth = 0;
        if (kind == kReturn || kind == kReturnGo) {
            // 'return' arms keep their AstReturn / exit-jump form, so no
            // tail-position requirement -- but they must live in a function
            // whose return variable width matches the arm constants.
            if (!m_ftaskp || !m_ftaskp->isFunction()) return false;
            const AstVar* const fvarp = VN_CAST(m_ftaskp->fvarp(), Var);
            if (!fvarp) return false;
            targetWidth = fvarp->width();
        } else {
            targetWidth = lhsp->width();
        }
        if (valueWidth != targetWidth || valueWidth > kCaseTableMaxValueWidth) return false;

        // Build the ConstPool table. The initializer is cloned into the pool
        // entry by findTable; initp stays ours to delete either way.
        FileLine* const fl = nodep->fileline();
        AstNodeDType* const elemDTypep
            = nodep->findBitDType(valueWidth, valueWidth, VSigning::UNSIGNED);
        AstUnpackArrayDType* const tableDTypep = new AstUnpackArrayDType{
            fl, elemDTypep, new AstRange{fl, static_cast<int>(tableSize) - 1, 0}};
        v3Global.rootp()->typeTablep()->addTypesp(tableDTypep);
        AstNodeExpr* const defaultExprp
            = defaultValp ? static_cast<AstNodeExpr*>(defaultValp->cloneTree(false))
                          : static_cast<AstNodeExpr*>(
                              new AstConst{fl, AstConst::WidthedValue{}, valueWidth, 0});
        AstInitArray* const initp = new AstInitArray{fl, tableDTypep, defaultExprp};
        for (const auto& pair : values) {
            initp->addIndexValuep(pair.first, new AstConst{fl, pair.second->num()});
        }
        AstVarScope* const tableVscp = v3Global.rootp()->constPoolp()->findTable(initp);
        initp->deleteTree();

        AstNodeExpr* const newRhs
            = new AstArraySel{fl, new AstVarRef{fl, tableVscp, VAccess::READ},
                              exprp->cloneTree(false)};
        AstNode* newStmtp = nullptr;
        if (kind == kReturn) {
            newStmtp = new AstReturn{fl, newRhs};
        } else if (kind == kReturnGo) {
            // Assign the return variable from the table, then keep the
            // shared function-exit jump so 'return' semantics are preserved.
            newStmtp = new AstAssign{fl, lhsp->cloneTree(false), newRhs};
            newStmtp->addNext(firstJumpGp->cloneTree(false));
        } else if (kind == kAssignDly) {
            newStmtp = new AstAssignDly{fl, lhsp->cloneTree(false), newRhs};
        } else {
            newStmtp = new AstAssign{fl, lhsp->cloneTree(false), newRhs};
        }
        nodep->replaceWith(newStmtp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        UINFO(4, "  Case table " << tableVscp->varp()->name() << " idxw" << indexWidth
                                 << " arms" << nArms << endl);
        return true;
    }

    // VISITORS
    void visit(AstCase* nodep) override {
        V3Case::caseLint(nodep);
        iterateChildren(nodep);
        if (debug() >= 9) nodep->dumpTree("-  case_old: ");
        if (v3Global.opt.fCaseTable() && tryCaseTable(nodep)) {
            ++m_statCaseTable;
            return;
        }
        if (isCaseTreeFast(nodep) && v3Global.opt.fCase()) {
            // It's a simple priority encoder or complete statement
            // we can make a tree of statements to avoid extra comparisons
            ++m_statCaseFast;
            VL_DO_DANGLING(replaceCaseFast(nodep), nodep);
        } else {
            // If a case statement is whole, presume signals involved aren't forming a latch
            if (m_alwaysp) m_alwaysp->fileline()->warnOff(V3ErrorCode::LATCH, true);
            ++m_statCaseSlow;
            VL_DO_DANGLING(replaceCaseComplicated(nodep), nodep);
        }
    }
    //--------------------
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override {
        if (VN_IS(nodep, Always)) m_alwaysp = nodep;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CaseVisitor(AstNetlist* nodep) {
        for (auto& itr : m_valueItem) itr = nullptr;
        iterate(nodep);
    }
    ~CaseVisitor() override {
        V3Stats::addStat("Optimizations, Cases parallelized", m_statCaseFast);
        V3Stats::addStat("Optimizations, Cases complex", m_statCaseSlow);
        V3Stats::addStat("Optimizations, Cases to lookup tables", m_statCaseTable);
    }
};

//######################################################################
// Case class functions

void V3Case::caseAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CaseVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("case", 0, dumpTree() >= 3);
}
void V3Case::caseLint(AstNodeCase* nodep) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    { CaseLintVisitor{nodep}; }
}
