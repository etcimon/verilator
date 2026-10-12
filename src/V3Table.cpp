// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Make lookup tables
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
// TABLE TRANSFORMATIONS:
//      Look at all large always and assignments.
//      Count # of input bits and # of output bits, and # of statements
//      If high # of statements relative to inpbits*outbits,
//      replace with lookup table.
//      A wide input (a decoder) is sliced: each output is tabled on only
//      the input bits its expression actually reads, so a 32-bit
//      instruction becomes a few small indexes instead of one 2^32 table.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Table.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Simulate.h"
#include "V3Stats.h"

#include <cmath>
#include <map>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Table class functions

// CONFIG
// 1MB is max table size (better be lots of instructs to be worth it!)
static constexpr int TABLE_MAX_BYTES = 1 * 1024 * 1024;
// 64MB is close to max memory of some systems (256MB or so), so don't get out of control
static constexpr int TABLE_TOTAL_BYTES = 64 * 1024 * 1024;
// Worth no more than 8 bytes of data to replace an instruction
static constexpr int TABLE_SPACE_TIME_MULT = 8;
// If < 32 instructions, not worth the effort
static constexpr int TABLE_MIN_NODE_COUNT = 32;
// Assume an instruction is 4 bytes
static constexpr int TABLE_BYTES_PER_INST = 4;

//######################################################################

class TableVisitor;

class TableSimulateVisitor final : public SimulateVisitor {
    // MEMBERS
    TableVisitor* const m_cbthis;  ///< Class for callback

public:
    ///< Call other-this function on all new var references
    void varRefCb(AstVarRef* nodep) override;

    // CONSTRUCTORS
    explicit TableSimulateVisitor(TableVisitor* cbthis)
        : m_cbthis{cbthis} {}
    ~TableSimulateVisitor() override = default;
};

//######################################################################
// Class for holding lookup table state during construction

class TableBuilder final {
    FileLine* const m_fl;  // FileLine used during construction
    AstInitArray* m_initp = nullptr;  // The lookup table initializer values
    AstVarScope* m_varScopep = nullptr;  // The scoped variable holding the table

public:
    explicit TableBuilder(FileLine* fl)
        : m_fl{fl} {}

    ~TableBuilder() {
        if (m_initp) m_initp->deleteTree();
    }

    void setTableSize(AstNodeDType* elemDType, unsigned size) {
        UASSERT_OBJ(!m_initp, m_fl, "Table size already set");
        UASSERT_OBJ(size > 0, m_fl, "Size zero");
        // TODO: Assert elemDType is a packed type
        // Create data type
        const int width = elemDType->width();
        AstNodeDType* const subDTypep
            = elemDType->isString()
                  ? elemDType
                  : v3Global.rootp()->findBitDType(width, width, VSigning::UNSIGNED);
        AstUnpackArrayDType* const tableDTypep = new AstUnpackArrayDType{
            m_fl, subDTypep, new AstRange{m_fl, static_cast<int>(size), 0}};
        v3Global.rootp()->typeTablep()->addTypesp(tableDTypep);
        // Create table initializer (with default value 0)
        AstConst* const defaultp = elemDType->isString()
                                       ? new AstConst{m_fl, AstConst::String{}, ""}
                                       : new AstConst{m_fl, AstConst::WidthedValue{}, width, 0};
        m_initp = new AstInitArray{m_fl, tableDTypep, defaultp};
    }

    void addValue(unsigned index, const V3Number& value) {
        UASSERT_OBJ(!m_varScopep, m_fl, "Table variable already created");
        // Default value is zero/empty string so don't add it
        if (value.isString() ? value.toString().empty() : value.isEqZero()) return;
        m_initp->addIndexValuep(index, new AstConst{m_fl, value});
    }

    AstVarScope* varScopep() {
        if (!m_varScopep) { m_varScopep = v3Global.rootp()->constPoolp()->findTable(m_initp); }
        return m_varScopep;
    }
};

//######################################################################
// Class for holding output variable state during table conversion of logic

class TableOutputVar final {
    AstVarScope* const m_varScopep;  // The output variable
    const unsigned m_ord;  // Output ordinal number in this block
    bool m_mayBeUnassigned = false;  // If true, then this variable may be unassigned through
                                     // some path through the block being table converted
    TableBuilder m_tableBuilder;

public:
    TableOutputVar(AstVarScope* varScopep, unsigned ord)
        : m_varScopep{varScopep}
        , m_ord{ord}
        , m_tableBuilder{varScopep->fileline()} {}

    AstVarScope* varScopep() const { return m_varScopep; }
    string name() const { return varScopep()->varp()->name(); }
    unsigned ord() const { return m_ord; }
    void setMayBeUnassigned() { m_mayBeUnassigned = true; }
    bool mayBeUnassigned() const { return m_mayBeUnassigned; }
    void setTableSize(unsigned size) { m_tableBuilder.setTableSize(varScopep()->dtypep(), size); }
    void addValue(unsigned index, const V3Number& value) { m_tableBuilder.addValue(index, value); }
    AstVarScope* tabeVarScopep() { return m_tableBuilder.varScopep(); }
};

//######################################################################
// Table class functions

class TableVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on each always/assignw

    // STATE
    double m_totalBytes = 0;  // Total bytes in tables created
    VDouble0 m_statTablesCre;  // Statistic tracking
    VDouble0 m_statSlices;  // Sliced tables (one per independent input mask)

    //  State cleared on each module
    AstNodeModule* m_modp = nullptr;  // Current MODULE
    int m_modTables = 0;  // Number of tables created in this module

    //  State cleared on each scope
    AstScope* m_scopep = nullptr;  // Current SCOPE

    //  State cleared on each always/assignw
    bool m_assignDly = false;  // Consists of delayed assignments instead of normal assignments
    unsigned m_inWidthBits = 0;  // Input table width - in bits
    unsigned m_outWidthBytes = 0;  // Output table width - in bytes
    std::vector<AstVarScope*> m_inVarps;  // Input variable list
    std::vector<TableOutputVar> m_outVarps;  // Output variable list
    string m_why;  // Why the full table was refused, empty if it was accepted
    int m_instrs = 0;  // Instruction nodes in the block under test
    int m_dataCount = 0;

    // METHODS

public:
    void simulateVarRefCb(AstVarRef* nodep) {
        // Called by TableSimulateVisitor on each unique varref encountered
        UINFO(9, "   SimVARREF " << nodep << endl);
        AstVarScope* const vscp = nodep->varScopep();
        if (nodep->access().isWriteOrRW()) {
            // We'll make the table with a separate natural alignment for each output var, so
            // always have 8, 16 or 32 bit widths, so use widthTotalBytes
            m_outWidthBytes += nodep->varp()->dtypeSkipRefp()->widthTotalBytes();
            m_outVarps.emplace_back(vscp, m_outVarps.size());
        }
        if (nodep->access().isReadOrRW()) {
            m_inWidthBits += nodep->varp()->width();
            m_inVarps.push_back(vscp);
        }
    }

private:
    bool treeTest(AstAlways* nodep) {
        // Process alw/assign tree
        m_inWidthBits = 0;
        m_outWidthBytes = 0;
        m_inVarps.clear();
        m_outVarps.clear();

        // Collect stats
        TableSimulateVisitor chkvis{this};
        chkvis.mainTableCheck(nodep);
        m_assignDly = chkvis.isAssignDly();
        // Also sets m_inWidthBits
        // Also sets m_outWidthBytes
        // Also sets m_inVarps
        // Also sets m_outVarps

        // Calc data storage in bytes
        const size_t chgWidth = m_outVarps.size();
        const double space = std::pow<double>(2.0, m_inWidthBits) * (m_outWidthBytes + chgWidth);
        // Instruction count bytes (ok, it's space also not time :)
        const double time  // max(_, 1), so we won't divide by zero
            = std::max<double>(chkvis.instrCount() * TABLE_BYTES_PER_INST + chkvis.dataCount(), 1);
        if (chkvis.instrCount() < TABLE_MIN_NODE_COUNT) {
            chkvis.clearOptimizable(nodep, "Table has too few nodes involved");
        }
        if (space > TABLE_MAX_BYTES) {
            chkvis.clearOptimizable(nodep, "Table takes too much space");
        }
        if (space > time * TABLE_SPACE_TIME_MULT) {
            chkvis.clearOptimizable(nodep, "Table has bad tradeoff");
        }
        if (m_totalBytes > TABLE_TOTAL_BYTES) {
            chkvis.clearOptimizable(nodep, "Table out of memory");
        }
        if (!m_outWidthBytes || !m_inWidthBits) {
            chkvis.clearOptimizable(nodep, "Table has no outputs");
        }
        if (chkvis.isOutputter()) {
            chkvis.clearOptimizable(nodep, "Table creates display output");
        }
        UINFO(4, "  Test: Opt=" << (chkvis.optimizable() ? "OK" : "NO") << ", Instrs="
                                << chkvis.instrCount() << " Data=" << chkvis.dataCount()
                                << " in width (bits)=" << m_inWidthBits << " out width (bytes)="
                                << m_outWidthBytes << " Spacetime=" << (space / time) << "("
                                << space << "/" << time << ")"
                                << ": " << nodep << endl);
        m_instrs = chkvis.instrCount();
        m_dataCount = chkvis.dataCount();
        m_why = chkvis.optimizable() ? "" : chkvis.whyNotMessage();
        if (chkvis.optimizable()) {
            UINFO(3, " Table Optimize spacetime=" << (space / time) << " " << nodep << endl);
            m_totalBytes += space;
        }
        return chkvis.optimizable();
    }

    void replaceWithTable(AstAlways* nodep) {
        // We've determined this table of nodes is optimizable, do it.
        ++m_modTables;
        ++m_statTablesCre;

        FileLine* const fl = nodep->fileline();

        // We will need a table index variable, create it here.
        AstVar* const indexVarp
            = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtableidx" + cvtToStr(m_modTables),
                         VFlagBitPacked{}, static_cast<int>(m_inWidthBits)};
        m_modp->addStmtsp(indexVarp);
        AstVarScope* const indexVscp = new AstVarScope{indexVarp->fileline(), m_scopep, indexVarp};
        m_scopep->addVarsp(indexVscp);

        // The 'output assigned' table builder
        TableBuilder outputAssignedTableBuilder{fl};
        outputAssignedTableBuilder.setTableSize(
            nodep->findBitDType(m_outVarps.size(), m_outVarps.size(), VSigning::UNSIGNED),
            VL_MASK_I(m_inWidthBits));

        // Set sizes of output tables
        for (TableOutputVar& tov : m_outVarps) { tov.setTableSize(VL_MASK_I(m_inWidthBits)); }

        // Populate the tables
        createTables(nodep, outputAssignedTableBuilder);

        AstNode* const stmtsp = createLookupInput(fl, indexVscp);
        createOutputAssigns(nodep, stmtsp, indexVscp, outputAssignedTableBuilder.varScopep());

        // Link it in.
        // Keep sensitivity list, but delete all else
        nodep->stmtsp()->unlinkFrBackWithNext()->deleteTree();
        nodep->addStmtsp(stmtsp);
        if (debug() >= 6) nodep->dumpTree("-  table_new: ");
    }

    void createTables(AstAlways* nodep, TableBuilder& outputAssignedTableBuilder) {
        // Create table
        // There may be a simulation path by which the output doesn't change value.
        // We could bail on these cases, or we can have a "change it" boolean.
        // We've chosen the latter route, since recirc is common in large FSMs.
        TableSimulateVisitor simvis{this};
        for (uint32_t i = 0; i <= VL_MASK_I(m_inWidthBits); ++i) {
            const uint32_t inValue = i;
            // Make a new simulation structure so we can set new input values
            UINFO(8, " Simulating " << std::hex << inValue << endl);

            // Above simulateVisitor clears user 3, so
            // all outputs default to nullptr to mean 'recirculating'.
            simvis.clear();

            // Set all inputs to the constant
            uint32_t shift = 0;
            for (AstVarScope* invscp : m_inVarps) {
                // LSB is first variable, so extract it that way
                const AstConst cnst{invscp->fileline(), AstConst::WidthedValue{}, invscp->width(),
                                    VL_MASK_I(invscp->width()) & (inValue >> shift)};
                simvis.newValue(invscp, &cnst);
                shift += invscp->width();
                // We are using 32 bit arithmetic, because there's no way the input table can be
                // 2^32 bytes!
                UASSERT_OBJ(shift <= 32, nodep, "shift overflow");
                UINFO(8, "   Input " << invscp->name() << " = " << cnst.name() << endl);
            }

            // Simulate
            simvis.mainTableEmulate(nodep);
            UASSERT_OBJ(simvis.optimizable(), simvis.whyNotNodep(),
                        "Optimizable cleared, even though earlier test run said not: "
                            << simvis.whyNotMessage());

            // Build output value tables and the assigned flags table
            V3Number outputAssignedMask{nodep, static_cast<int>(m_outVarps.size()), 0};
            for (TableOutputVar& tov : m_outVarps) {
                if (V3Number* const outnump = simvis.fetchOutNumberNull(tov.varScopep())) {
                    UINFO(8, "   Output " << tov.name() << " = " << *outnump << endl);
                    outputAssignedMask.setBit(tov.ord(), 1);  // Mark output as assigned
                    tov.addValue(inValue, *outnump);
                } else {
                    UINFO(8, "   Output " << tov.name() << " not set for this input\n");
                    tov.setMayBeUnassigned();
                }
            }

            // Set changed table
            outputAssignedTableBuilder.addValue(inValue, outputAssignedMask);
        }  // each value
    }

    AstNode* createLookupInput(FileLine* fl, AstVarScope* indexVscp) {
        // Concat inputs into a single temp variable (inside always)
        // First var in inVars becomes the LSB of the concat
        AstNodeExpr* concatp = nullptr;
        for (AstVarScope* invscp : m_inVarps) {
            AstVarRef* const refp = new AstVarRef{fl, invscp, VAccess::READ};
            if (concatp) {
                concatp = new AstConcat{fl, refp, concatp};
            } else {
                concatp = refp;
            }
        }

        return new AstAssign{fl, new AstVarRef{fl, indexVscp, VAccess::WRITE}, concatp};
    }

    AstArraySel* select(FileLine* fl, AstVarScope* fromp, AstVarScope* indexp) {
        AstVarRef* const fromRefp = new AstVarRef{fl, fromp, VAccess::READ};
        AstVarRef* const indexRefp = new AstVarRef{fl, indexp, VAccess::READ};
        return new AstArraySel{fl, fromRefp, indexRefp};
    }

    void createOutputAssigns(AstNode* nodep, AstNode* stmtsp, AstVarScope* indexVscp,
                             AstVarScope* outputAssignedTableVscp) {
        FileLine* const fl = nodep->fileline();
        for (TableOutputVar& tov : m_outVarps) {
            AstNodeExpr* const alhsp = new AstVarRef{fl, tov.varScopep(), VAccess::WRITE};
            AstNodeExpr* const arhsp = select(fl, tov.tabeVarScopep(), indexVscp);
            AstNode* outsetp = m_assignDly
                                   ? static_cast<AstNode*>(new AstAssignDly{fl, alhsp, arhsp})
                                   : static_cast<AstNode*>(new AstAssign{fl, alhsp, arhsp});

            // If this output is unassigned on some code paths, wrap the assignment in an If
            if (tov.mayBeUnassigned()) {
                V3Number outputChgMask{nodep, static_cast<int>(m_outVarps.size()), 0};
                outputChgMask.setBit(tov.ord(), 1);
                AstNodeExpr* const condp
                    = new AstAnd{fl, select(fl, outputAssignedTableVscp, indexVscp),
                                 new AstConst{fl, outputChgMask}};
                outsetp = new AstIf{fl, condp, outsetp};
            }

            stmtsp->addNext(outsetp);
        }
    }

    // A value's dependence on the unique input bits of this block.
    // identity means value bit i is input bit (identBase + i), so a constant
    // select can shrink the mask. Anything that mixes bits clears identity
    // and keeps the union, which is still a conservative support.
    struct ExprBits final {
        uint64_t mask = 0;
        bool identity = false;
        int identBase = 0;
        int width = 0;
    };

    struct InBit final {
        AstVarScope* vscp;
        int local;
    };

    bool sliceCandidate() const {
        if (m_why.find("too much space") == string::npos
            && m_why.find("bad tradeoff") == string::npos) {
            return false;
        }
        if (m_outVarps.empty() || m_inVarps.empty()) return false;
        return true;
    }

    ExprBits* exprBits(AstNode* nodep, const std::unordered_map<AstVarScope*, int>& base,
                       int nBits, ExprBits& storage) {
        storage = {};
        if (!nodep || VN_IS(nodep, Const)) return &storage;
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (!refp->access().isReadOrRW()) return &storage;
            const auto it = base.find(refp->varScopep());
            if (it == base.end()) return nullptr;
            const int width = refp->varp()->width();
            if (it->second < 0 || width <= 0 || it->second + width > nBits || nBits > 64) {
                return nullptr;
            }
            storage.identity = true;
            storage.identBase = it->second;
            storage.width = width;
            storage.mask = width >= 64 ? ~0ull : ((1ull << width) - 1) << it->second;
            return &storage;
        }
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            // A select of a zero-extended input is still that input's low bits.
            AstNode* fromp = selp->fromp();
            while (VN_IS(fromp, Extend) || VN_IS(fromp, CCast)) {
                fromp = VN_CAST(fromp, NodeUniop)->lhsp();
            }
            ExprBits innerStore;
            ExprBits* const innerp = exprBits(fromp, base, nBits, innerStore);
            if (!innerp) return nullptr;
            if (!innerp->identity || !VN_IS(selp->lsbp(), Const) || !VN_IS(selp->widthp(), Const)) {
                storage.mask = innerp->mask;
                return &storage;
            }
            const int lsb = selp->lsbConst();
            const int width = selp->widthConst();
            if (lsb < 0 || width <= 0 || lsb + width > innerp->width) {
                storage.mask = innerp->mask;
                return &storage;
            }
            storage.identity = true;
            storage.identBase = innerp->identBase + lsb;
            storage.width = width;
            storage.mask = width >= 64 ? ~0ull : ((1ull << width) - 1) << storage.identBase;
            return &storage;
        }
        if (AstCond* const condp = VN_CAST(nodep, Cond)) {
            ExprBits aStore;
            ExprBits bStore;
            ExprBits cStore;
            ExprBits* const ap = exprBits(condp->condp(), base, nBits, aStore);
            ExprBits* const bp = exprBits(condp->thenp(), base, nBits, bStore);
            ExprBits* const cp = exprBits(condp->elsep(), base, nBits, cStore);
            if (!ap || !bp || !cp) return nullptr;
            storage.mask = ap->mask | bp->mask | cp->mask;
            return &storage;
        }
        if (AstNodeBiop* const biop = VN_CAST(nodep, NodeBiop)) {
            ExprBits lStore;
            ExprBits rStore;
            ExprBits* const lp = exprBits(biop->lhsp(), base, nBits, lStore);
            ExprBits* const rp = exprBits(biop->rhsp(), base, nBits, rStore);
            if (!lp || !rp) return nullptr;
            storage.mask = lp->mask | rp->mask;
            return &storage;
        }
        if (AstNodeUniop* const unop = VN_CAST(nodep, NodeUniop)) {
            ExprBits childStore;
            ExprBits* const childp = exprBits(unop->lhsp(), base, nBits, childStore);
            if (!childp) return nullptr;
            storage.mask = childp->mask;
            return &storage;
        }
        return nullptr;
    }

    AstVarScope* writtenVar(AstNode* lhsp) {
        if (AstVarRef* const refp = VN_CAST(lhsp, VarRef)) return refp->varScopep();
        if (AstSel* const selp = VN_CAST(lhsp, Sel)) return writtenVar(selp->fromp());
        return nullptr;
    }

    int outIndexOf(AstVarScope* vscp) const {
        for (size_t i = 0; i < m_outVarps.size(); ++i) {
            if (m_outVarps[i].varScopep() == vscp) return static_cast<int>(i);
        }
        return -1;
    }

    // extraMask is the input bits of the conditions that guard this statement.
    bool walkSupport(AstNode* nodep, uint64_t extraMask,
                     const std::unordered_map<AstVarScope*, int>& base, int nBits,
                     std::vector<uint64_t>& support, std::vector<bool>& seen) {
        for (; nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, Comment) || VN_IS(nodep, Empty)) continue;
            if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
                if (!walkSupport(beginp->stmtsp(), extraMask, base, nBits, support, seen)) {
                    return false;
                }
                continue;
            }
            if (AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
                AstVarScope* const vscp = writtenVar(assignp->lhsp());
                const int idx = vscp ? outIndexOf(vscp) : -1;
                if (idx < 0) return false;
                ExprBits store;
                ExprBits* const rhsp = exprBits(assignp->rhsp(), base, nBits, store);
                if (!rhsp) return false;
                support[idx] |= extraMask | rhsp->mask;
                seen[idx] = true;
                continue;
            }
            if (AstIf* const ifp = VN_CAST(nodep, If)) {
                ExprBits store;
                ExprBits* const condp = exprBits(ifp->condp(), base, nBits, store);
                if (!condp) return false;
                const uint64_t next = extraMask | condp->mask;
                if (!walkSupport(ifp->thensp(), next, base, nBits, support, seen)) return false;
                if (!walkSupport(ifp->elsesp(), next, base, nBits, support, seen)) return false;
                continue;
            }
            if (AstCase* const casep = VN_CAST(nodep, Case)) {
                ExprBits store;
                ExprBits* const exprp = exprBits(casep->exprp(), base, nBits, store);
                if (!exprp) return false;
                const uint64_t next = extraMask | exprp->mask;
                for (AstCaseItem* itemp = casep->itemsp(); itemp;
                     itemp = VN_AS(itemp->nextp(), CaseItem)) {
                    uint64_t itemMask = next;
                    for (AstNodeExpr* condp = itemp->condsp(); condp;
                         condp = VN_AS(condp->nextp(), NodeExpr)) {
                        ExprBits condStore;
                        ExprBits* const gotp = exprBits(condp, base, nBits, condStore);
                        if (!gotp) return false;
                        itemMask |= gotp->mask;
                    }
                    if (!walkSupport(itemp->stmtsp(), itemMask, base, nBits, support, seen)) {
                        return false;
                    }
                }
                continue;
            }
            return false;
        }
        return true;
    }

    // Replace one always with one table per independent input-bit mask.
    bool trySlice(AstAlways* nodep) {
        if (!sliceCandidate()) return false;

        std::unordered_map<AstVarScope*, int> base;
        std::vector<InBit> bitOf;
        for (AstVarScope* const vscp : m_inVarps) {
            if (base.count(vscp)) continue;
            if (outIndexOf(vscp) >= 0) return false;  // Read and written: not a pure input
            const int width = vscp->width();
            if (width <= 0 || static_cast<int>(bitOf.size()) + width > 64) return false;
            base.emplace(vscp, static_cast<int>(bitOf.size()));
            for (int bit = 0; bit < width; ++bit) bitOf.push_back({vscp, bit});
        }
        const int nBits = static_cast<int>(bitOf.size());
        if (nBits <= 1) return false;

        std::vector<uint64_t> support(m_outVarps.size(), 0);
        std::vector<bool> seen(m_outVarps.size(), false);
        if (!walkSupport(nodep->stmtsp(), 0, base, nBits, support, seen)) return false;
        for (bool wasSeen : seen) {
            if (!wasSeen) return false;
        }

        std::map<uint64_t, std::vector<unsigned>> groups;
        for (unsigned i = 0; i < support.size(); ++i) groups[support[i]].push_back(i);

        struct Slice final {
            uint64_t mask;
            std::vector<int> bitPos;  // Global input bits, LSB of the index first
            std::vector<unsigned> outs;
            int width = 0;
            unsigned outBytes = 0;
        };
        std::vector<Slice> slices;
        double space = 0;
        for (const auto& group : groups) {
            Slice slice;
            slice.mask = group.first;
            slice.outs = group.second;
            for (int bit = 0; bit < nBits; ++bit) {
                if (slice.mask & (1ull << bit)) slice.bitPos.push_back(bit);
            }
            slice.width = static_cast<int>(slice.bitPos.size());
            if (slice.width > 16) return false;
            for (unsigned out : slice.outs) {
                slice.outBytes += m_outVarps[out].varScopep()->varp()->dtypeSkipRefp()
                                      ->widthTotalBytes();
            }
            const double entries = slice.width == 0 ? 1.0 : std::pow(2.0, slice.width);
            space += entries * (slice.outBytes + slice.outs.size());
            slices.push_back(std::move(slice));
        }
        const double time = std::max<double>(m_instrs * TABLE_BYTES_PER_INST + m_dataCount, 1);
        if (space > TABLE_MAX_BYTES || space > time * TABLE_SPACE_TIME_MULT) return false;
        if (m_totalBytes + space > TABLE_TOTAL_BYTES) return false;
        // A lone group that still uses every input bit is the table we refused.
        // A narrower group is a real slice even if it is the only lookup.
        // Width 0 is a constant assign, not a table.
        int nReal = 0;
        int realWidth = 0;
        for (const Slice& slice : slices) {
            if (slice.width <= 0) continue;
            ++nReal;
            realWidth = slice.width;
        }
        if (nReal == 0) return false;
        if (nReal == 1 && realWidth >= nBits) return false;

        // Simulate every slice before any AST edit. A later failure must not
        // leave index variables, half-built tables, or inflated stats behind.
        struct SimSlice final {
            std::vector<std::vector<V3Number>> values;
            std::vector<std::vector<bool>> assigned;
            std::vector<bool> anyHole;
        };
        std::vector<SimSlice> sims;
        sims.reserve(slices.size());
        {
            TableSimulateVisitor simvis{this};
            for (const Slice& slice : slices) {
                SimSlice sim;
                sim.values.resize(slice.outs.size());
                sim.assigned.resize(slice.outs.size());
                sim.anyHole.assign(slice.outs.size(), false);
                const uint32_t nIdx = slice.width == 0 ? 1u : (1u << slice.width);
                for (uint32_t idx = 0; idx < nIdx; ++idx) {
                    simvis.clear();
                    std::vector<V3Number> nums;
                    nums.reserve(base.size());
                    std::vector<AstVarScope*> vars;
                    vars.reserve(base.size());
                    for (const auto& pair : base) {
                        vars.push_back(pair.first);
                        nums.emplace_back(pair.first->fileline(), pair.first->width(), 0);
                    }
                    for (size_t k = 0; k < slice.bitPos.size(); ++k) {
                        if ((idx & (1u << k)) == 0) continue;
                        const InBit& in = bitOf[slice.bitPos[k]];
                        for (size_t v = 0; v < vars.size(); ++v) {
                            if (vars[v] == in.vscp) nums[v].setBit(in.local, 1);
                        }
                    }
                    for (size_t v = 0; v < vars.size(); ++v) {
                        const AstConst cnst{vars[v]->fileline(), nums[v]};
                        simvis.newValue(vars[v], &cnst);
                    }
                    simvis.mainTableEmulate(nodep);
                    if (!simvis.optimizable()) return false;
                    for (size_t o = 0; o < slice.outs.size(); ++o) {
                        TableOutputVar& tov = m_outVarps[slice.outs[o]];
                        if (V3Number* const outnump
                            = simvis.fetchOutNumberNull(tov.varScopep())) {
                            sim.values[o].push_back(*outnump);
                            sim.assigned[o].push_back(true);
                        } else {
                            sim.values[o].emplace_back(nodep, tov.varScopep()->width(), 0);
                            sim.assigned[o].push_back(false);
                            sim.anyHole[o] = true;
                        }
                    }
                }
                sims.push_back(std::move(sim));
            }
        }

        FileLine* const fl = nodep->fileline();
        AstNode* stmtsp = nullptr;
        const auto append = [&](AstNode* nodep) {
            if (!nodep) return;
            stmtsp = stmtsp ? AstNode::addNext(stmtsp, nodep) : nodep;
        };

        for (size_t s = 0; s < slices.size(); ++s) {
            Slice& slice = slices[s];
            SimSlice& sim = sims[s];
            // Constant support is a direct assign. It is not a lookup table.
            if (slice.width > 0) {
                ++m_modTables;
                ++m_statTablesCre;
                ++m_statSlices;
            }
            const uint32_t nIdx = slice.width == 0 ? 1u : (1u << slice.width);
            const uint32_t maxIdx = nIdx - 1;

            AstVarScope* indexVscp = nullptr;
            if (slice.width > 0) {
                AstVar* const indexVarp
                    = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtableslc" + cvtToStr(m_modTables),
                                 VFlagBitPacked{}, slice.width};
                m_modp->addStmtsp(indexVarp);
                indexVscp = new AstVarScope{fl, m_scopep, indexVarp};
                m_scopep->addVarsp(indexVscp);
                AstNodeExpr* concatp = nullptr;
                for (int global : slice.bitPos) {
                    const InBit& in = bitOf[global];
                    AstSel* const bitp = new AstSel{
                        fl, new AstVarRef{fl, in.vscp, VAccess::READ}, in.local, 1};
                    concatp = concatp ? new AstConcat{fl, bitp, concatp}
                                      : static_cast<AstNodeExpr*>(bitp);
                }
                append(new AstAssign{fl, new AstVarRef{fl, indexVscp, VAccess::WRITE}, concatp});
            }

            for (size_t o = 0; o < slice.outs.size(); ++o) {
                TableOutputVar& tov = m_outVarps[slice.outs[o]];
                if (slice.width == 0) {
                    if (!sim.assigned[o][0]) continue;
                    AstNodeExpr* const alhsp = new AstVarRef{fl, tov.varScopep(), VAccess::WRITE};
                    AstNodeExpr* const arhsp = new AstConst{fl, sim.values[o][0]};
                    append(m_assignDly ? static_cast<AstNode*>(new AstAssignDly{fl, alhsp, arhsp})
                                       : static_cast<AstNode*>(new AstAssign{fl, alhsp, arhsp}));
                    continue;
                }
                tov.setTableSize(maxIdx);
                if (sim.anyHole[o]) tov.setMayBeUnassigned();
                for (uint32_t idx = 0; idx < nIdx; ++idx) tov.addValue(idx, sim.values[o][idx]);

                TableBuilder holeBuilder{fl};
                AstVarScope* holeVscp = nullptr;
                if (sim.anyHole[o]) {
                    holeBuilder.setTableSize(nodep->findBitDType(1, 1, VSigning::UNSIGNED),
                                             maxIdx);
                    for (uint32_t idx = 0; idx < nIdx; ++idx) {
                        if (!sim.assigned[o][idx]) continue;
                        V3Number one{nodep, 1, 1};
                        holeBuilder.addValue(idx, one);
                    }
                    holeVscp = holeBuilder.varScopep();
                }

                AstNodeExpr* const alhsp = new AstVarRef{fl, tov.varScopep(), VAccess::WRITE};
                AstNodeExpr* const arhsp = select(fl, tov.tabeVarScopep(), indexVscp);
                AstNode* outsetp = m_assignDly
                                       ? static_cast<AstNode*>(new AstAssignDly{fl, alhsp, arhsp})
                                       : static_cast<AstNode*>(new AstAssign{fl, alhsp, arhsp});
                if (holeVscp) outsetp = new AstIf{fl, select(fl, holeVscp, indexVscp), outsetp};
                append(outsetp);
            }
        }

        m_totalBytes += space;
        UINFO(3, " Table slices " << slices.size() << " spacetime=" << (space / time) << " "
                                  << nodep << endl);
        nodep->stmtsp()->unlinkFrBackWithNext()->deleteTree();
        nodep->addStmtsp(stmtsp);
        return true;
    }

    // VISITORS
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modTables);
        {
            m_modp = nodep;
            m_modTables = 0;
            iterateChildren(nodep);
        }
    }
    void visit(AstScope* nodep) override {
        UINFO(4, " SCOPE " << nodep << endl);
        m_scopep = nodep;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    void visit(AstAlways* nodep) override {
        UINFO(4, "  ALWAYS  " << nodep << endl);
        if (treeTest(nodep)) {
            // Well, then, I'll be a memory hog.
            replaceWithTable(nodep);
        } else if (trySlice(nodep)) {
            // Wide input, independent fields. Each field is its own table.
        }
    }
    void visit(AstNodeAssign* nodep) override {
        // It's nearly impossible to have a large enough assign to make this worthwhile
        // For now we won't bother.
        // Accelerated: no iterate
    }

public:
    // CONSTRUCTORS
    explicit TableVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~TableVisitor() override {  //
        V3Stats::addStat("Optimizations, Tables created", m_statTablesCre);
        V3Stats::addStat("Optimizations, Table slices", m_statSlices);
    }
};

//######################################################################

void TableSimulateVisitor::varRefCb(AstVarRef* nodep) {
    // Called by checking on each new varref encountered
    // We cross-call into a TableVisitor function.
    m_cbthis->simulateVarRefCb(nodep);
}

//######################################################################
// Table class functions

void V3Table::tableAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TableVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("table", 0, dumpTree() >= 3);
}
