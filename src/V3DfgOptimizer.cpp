// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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
//
// High level entry points from Ast world to the DFG optimizer.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3DfgOptimizer.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// Match LSB first. Stop at the storage boundary; never traverse a variable's
// drivers or bypass a shared intermediate to make a projection look regular.
static bool matchPlane(const DfgVertex* vp, DfgVertex*& rowp, unsigned& first, unsigned& count) {
    if (const auto* const concatp = vp->cast<DfgConcat>()) {
        if (concatp->width() < 8 && concatp->hasMultipleSinks()) return false;
        return matchPlane(concatp->rhsp(), rowp, first, count)
               && matchPlane(concatp->lhsp(), rowp, first, count);
    }
    const auto* const selp = vp->cast<DfgSel>();
    if (!selp || selp->width() != 1 || selp->hasMultipleSinks()) return false;
    DfgVertex* const fromp = selp->fromp();
    if (!fromp->is<DfgVarPacked>() || fromp->width() != 64) return false;
    if (!count) {
        rowp = fromp;
        first = selp->lsb();
    }
    if (rowp != fromp || first >= 8 || selp->lsb() != first + 8 * count) return false;
    ++count;
    return true;
}

static unsigned packBytePlanes(DfgGraph& graph) {
    unsigned applied = 0;
    for (DfgVertex *vp = graph.opVerticesBeginp(), *nextp; vp; vp = nextp) {
        nextp = vp->verticesNext();
        if (!vp->is<DfgConcat>() || vp->width() != 8 || !vp->hasSinks()) continue;
        DfgVertex* rowp = nullptr;
        unsigned first = 0, count = 0;
        if (!matchPlane(vp, rowp, first, count) || count != 8) continue;
        FileLine* const flp = vp->fileline();
        AstNodeDType* const dtp = rowp->dtypep();
        const auto constant = [&](uint64_t value) {
            auto* const cp = new DfgConst{graph, flp, 64};
            cp->num().setQuad(value);
            return cp;
        };
        if (first) {
            auto* const shiftp = new DfgShiftR{graph, flp, dtp};
            shiftp->lhsp(rowp);
            shiftp->rhsp(new DfgConst{graph, flp, 32, first});
            rowp = shiftp;
        }
        auto* const maskp = new DfgAnd{graph, flp, dtp};
        maskp->lhsp(rowp);
        maskp->rhsp(constant(0x0101010101010101ULL));
        // Each selected bit 8*i contributes to 56+i via multiplier bit
        // 56-7*i. The 8-by-8 partial products occupy distinct positions.
        auto* const mulp = new DfgMul{graph, flp, dtp};
        mulp->lhsp(maskp);
        mulp->rhsp(constant(0x0102040810204080ULL));
        auto* const resultp = new DfgSel{graph, flp, vp->dtypep()};
        resultp->fromp(mulp);
        resultp->lsb(56);
        vp->replaceWith(resultp);
        vp->unlinkDelete(graph);
        ++applied;
    }
    return applied;
}

namespace {
// One bit of valid & ~(veto & broadcast). Never follow a variable's drivers;
// a shared one-bit gate (including a select) is safe to read at the same site.
struct PredicateLane final {
    DfgVertex* validp;
    DfgSel* vetop;
    DfgVertex* gatep;
};

// Accept identical scalar reads even when CSE has not yet coalesced them.
static bool sameGate(DfgVertex* ap, DfgVertex* bp) {
    if (ap == bp) return true;
    if (const auto* const an = ap->cast<DfgNot>()) {
        const auto* const bn = bp->cast<DfgNot>();
        if (!bn) return false;
        ap = an->srcp();
        bp = bn->srcp();
        if (ap == bp) return true;
    }
    const auto* const a = ap->cast<DfgSel>();
    const auto* const b = bp->cast<DfgSel>();
    return a && b && a->fromp() == b->fromp() && a->lsb() == b->lsb()
           && a->width() == b->width();
}

static bool matchPredicateLane(DfgVertex* vp, std::vector<PredicateLane>& lanes) {
    if (auto* const cp = vp->cast<DfgConcat>()) {
        return !cp->hasMultipleSinks() && matchPredicateLane(cp->rhsp(), lanes)
               && matchPredicateLane(cp->lhsp(), lanes);
    }
    auto* const outerp = vp->cast<DfgAnd>();
    if (!outerp || outerp->width() != 1 || outerp->hasMultipleSinks()) return false;
    const bool reverse = outerp->lhsp()->is<DfgNot>();
    auto* const validp = reverse ? outerp->rhsp() : outerp->lhsp();
    auto* const notp = (reverse ? outerp->lhsp() : outerp->rhsp())->cast<DfgNot>();
    if ((!validp->is<DfgSel>() && !validp->is<DfgVarPacked>()) || !notp
        || notp->hasMultipleSinks()) return false;
    auto* const innerp = notp->srcp()->cast<DfgAnd>();
    if (!innerp || innerp->hasMultipleSinks()) return false;
    for (unsigned swap = 0; swap < 2; ++swap) {
        auto* const vetop = (swap ? innerp->rhsp() : innerp->lhsp())->cast<DfgSel>();
        auto* const gatep = swap ? innerp->lhsp() : innerp->rhsp();
        if (!vetop || gatep->width() != 1 || validp->width() != 1 || vetop->width() != 1
            || !vetop->fromp()->is<DfgVarPacked>()) {
            continue;
        }
        if (!lanes.empty()) {
            const PredicateLane& base = lanes.front();
            if (base.vetop->fromp() != vetop->fromp()
                || vetop->lsb() != base.vetop->lsb() + lanes.size()
                || !sameGate(gatep, base.gatep)) {
                continue;
            }
        }
        lanes.push_back({validp, vetop, gatep});
        return true;
    }
    return false;
}

static unsigned packPredicates(DfgGraph& graph) {
    unsigned count = 0;
    for (DfgVertex *vp = graph.opVerticesBeginp(), *nextp; vp; vp = nextp) {
        nextp = vp->verticesNext();
        if (!vp->is<DfgConcat>() || vp->width() < 8 || vp->width() > 64 || !vp->hasSinks()
            || vp->findSink<DfgConcat>([](const DfgConcat& p) { return p.width() <= 64; })) {
            continue;
        }
        std::vector<PredicateLane> lanes;
        if (!matchPredicateLane(vp, lanes) || lanes.size() != vp->width()) continue;
        const auto& base = lanes.front();
        if (uint64_t{base.vetop->lsb()} + lanes.size() > base.vetop->fromp()->width()) continue;
        FileLine* const flp = vp->fileline();
        AstNodeDType* const dtp = vp->dtypep();
        const auto slice = [&](DfgSel* firstp) {
            auto* const selp = new DfgSel{graph, flp, dtp};
            selp->fromp(firstp->fromp());
            selp->lsb(firstp->lsb());
            return selp;
        };
        // Sign-extending exactly one bit broadcasts it to every output bit.
        auto* const broadp = new DfgExtendS{graph, flp, dtp};
        broadp->srcp(base.gatep);
        auto* const maskp = new DfgAnd{graph, flp, dtp};
        maskp->lhsp(slice(base.vetop));
        maskp->rhsp(broadp);
        auto* const notp = new DfgNot{graph, flp, dtp};
        notp->srcp(maskp);
        auto* const resultp = new DfgAnd{graph, flp, dtp};
        // Do not look through scalar valid wires. Reuse their values in order;
        // normal DFG inlining and adjacent-select folding can simplify the concat.
        DfgVertex* validp = base.validp;
        for (unsigned i = 1; i < lanes.size(); ++i) {
            auto* const cp = new DfgConcat{graph, flp, DfgVertex::dtypeForWidth(i + 1)};
            cp->lhsp(lanes[i].validp);
            cp->rhsp(validp);
            validp = cp;
        }
        resultp->lhsp(validp);
        resultp->rhsp(notp);
        vp->replaceWith(resultp);
        vp->unlinkDelete(graph);
        ++count;
    }
    return count;
}

// Match one bit of a 2-way bitwise mux:
//   (sel & a[i]) | (~sel & b[i])   or   sel ? a[i] : b[i]
// with a shared 1-bit `sel` and ascending contiguous packed slices of `a` and `b`.
struct BitwiseMuxInfo final {
    DfgVertex* selp = nullptr;
    DfgVarPacked* thenVarp = nullptr;
    DfgVarPacked* elseVarp = nullptr;
    unsigned thenLsb = 0;
    unsigned elseLsb = 0;
    unsigned count = 0;
};

static bool matchMuxArm(DfgVertex* arm, DfgVertex*& selp, bool& inverted, DfgSel*& dataSelp) {
    auto* const andp = arm->cast<DfgAnd>();
    if (!andp || andp->width() != 1 || andp->hasMultipleSinks()) return false;
    for (unsigned swap = 0; swap < 2; ++swap) {
        DfgVertex* const sp = swap ? andp->rhsp() : andp->lhsp();
        auto* const dp = (swap ? andp->lhsp() : andp->rhsp())->cast<DfgSel>();
        if (!dp || dp->width() != 1 || !dp->fromp()->is<DfgVarPacked>()) continue;
        if (auto* const notp = sp->cast<DfgNot>()) {
            if (notp->srcp()->width() == 1) {
                selp = notp->srcp();
                inverted = true;
                dataSelp = dp;
                return true;
            }
        } else if (sp->width() == 1) {
            selp = sp;
            inverted = false;
            dataSelp = dp;
            return true;
        }
    }
    return false;
}

static bool matchBitwiseMuxLane(DfgVertex* vp, BitwiseMuxInfo& info) {
    if (auto* const cp = vp->cast<DfgConcat>()) {
        return !cp->hasMultipleSinks() && matchBitwiseMuxLane(cp->rhsp(), info)
               && matchBitwiseMuxLane(cp->lhsp(), info);
    }
    DfgVertex* selp = nullptr;
    DfgSel* thenSelp = nullptr;
    DfgSel* elseSelp = nullptr;
    if (auto* const condp = vp->cast<DfgCond>()) {
        if (condp->width() != 1 || condp->hasMultipleSinks() || condp->condp()->width() != 1) {
            return false;
        }
        selp = condp->condp();
        thenSelp = condp->thenp()->cast<DfgSel>();
        elseSelp = condp->elsep()->cast<DfgSel>();
        if (!thenSelp || !elseSelp || thenSelp->width() != 1 || elseSelp->width() != 1) {
            return false;
        }
    } else if (auto* const orp = vp->cast<DfgOr>()) {
        if (orp->width() != 1 || orp->hasMultipleSinks()) return false;
        DfgVertex *s0 = nullptr, *s1 = nullptr;
        bool inv0 = false, inv1 = false;
        DfgSel *d0 = nullptr, *d1 = nullptr;
        if (!matchMuxArm(orp->lhsp(), s0, inv0, d0) || !matchMuxArm(orp->rhsp(), s1, inv1, d1)) {
            return false;
        }
        if (inv0 == inv1 || !sameGate(s0, s1)) return false;
        selp = inv0 ? s1 : s0;
        thenSelp = inv0 ? d1 : d0;
        elseSelp = inv0 ? d0 : d1;
    } else {
        return false;
    }
    auto* const tvarp = thenSelp->fromp()->cast<DfgVarPacked>();
    auto* const evarp = elseSelp->fromp()->cast<DfgVarPacked>();
    if (!tvarp || !evarp) return false;
    if (info.count == 0) {
        info.selp = selp;
        info.thenVarp = tvarp;
        info.elseVarp = evarp;
        info.thenLsb = thenSelp->lsb();
        info.elseLsb = elseSelp->lsb();
    } else {
        if (!sameGate(selp, info.selp) || tvarp != info.thenVarp || evarp != info.elseVarp
            || thenSelp->lsb() != info.thenLsb + info.count
            || elseSelp->lsb() != info.elseLsb + info.count) {
            return false;
        }
    }
    ++info.count;
    return true;
}

static unsigned packBitwiseMux(DfgGraph& graph) {
    unsigned applied = 0;
    for (DfgVertex *vp = graph.opVerticesBeginp(), *nextp; vp; vp = nextp) {
        nextp = vp->verticesNext();
        if (!vp->is<DfgConcat>() || vp->width() < 8 || vp->width() > 64 || !vp->hasSinks()
            || vp->findSink<DfgConcat>([](const DfgConcat& p) { return p.width() <= 64; })) {
            continue;
        }
        BitwiseMuxInfo info;
        if (!matchBitwiseMuxLane(vp, info) || info.count != vp->width()) continue;
        if (uint64_t{info.thenLsb} + info.count > info.thenVarp->width()
            || uint64_t{info.elseLsb} + info.count > info.elseVarp->width()) {
            continue;
        }
        FileLine* const flp = vp->fileline();
        AstNodeDType* const dtp = vp->dtypep();
        auto* const tSlicep = new DfgSel{graph, flp, dtp};
        tSlicep->fromp(info.thenVarp);
        tSlicep->lsb(info.thenLsb);
        auto* const eSlicep = new DfgSel{graph, flp, dtp};
        eSlicep->fromp(info.elseVarp);
        eSlicep->lsb(info.elseLsb);
        auto* const condp = new DfgCond{graph, flp, dtp};
        condp->condp(info.selp);
        condp->thenp(tSlicep);
        condp->elsep(eSlicep);
        vp->replaceWith(condp);
        vp->unlinkDelete(graph);
        ++applied;
    }
    return applied;
}

// Each lane tests one mask bit and reduces a whole word against the same
// mask. An empty mask makes every result zero regardless of the word data.
static bool matchGuardedReductions(DfgVertex* vp, DfgVertex*& maskp, unsigned& bit) {
    if (vp->hasMultipleSinks()) return false;
    if (auto* const cp = vp->cast<DfgConcat>()) {
        return matchGuardedReductions(cp->rhsp(), maskp, bit)
               && matchGuardedReductions(cp->lhsp(), maskp, bit);
    }
    auto* const lane = vp->cast<DfgAnd>();
    if (!lane || lane->width() != 1) return false;
    const bool swap = lane->rhsp()->is<DfgSel>();
    auto* const sel = (swap ? lane->rhsp() : lane->lhsp())->cast<DfgSel>();
    if (!sel || sel->width() != 1 || sel->lsb() != bit || !sel->fromp()->is<DfgVarPacked>()) {
        return false;
    }
    if (!maskp) maskp = sel->fromp();
    if (maskp != sel->fromp()) return false;
    auto* rhsp = swap ? lane->lhsp() : lane->rhsp();
    if (auto* const neg = rhsp->cast<DfgNot>()) {
        if (neg->hasMultipleSinks()) return false;
        rhsp = neg->srcp();
    }
    auto* const red = rhsp->cast<DfgRedOr>();
    if (!red || red->hasMultipleSinks()) return false;
    auto* const ap = red->srcp()->cast<DfgAnd>();
    if (!ap || ap->hasMultipleSinks() || (ap->lhsp() != maskp && ap->rhsp() != maskp)) {
        return false;
    }
    ++bit;
    return true;
}

static unsigned guardEmptyMasks(DfgGraph& graph) {
    unsigned count = 0;
    for (DfgVertex* vp = graph.opVerticesBeginp(); vp; vp = vp->verticesNext()) {
        if (!vp->is<DfgConcat>() || vp->width() < 8 || vp->width() > 64
            || !vp->findSink<DfgVarPacked>()) continue;
        DfgVertex* maskp = nullptr;
        unsigned bits = 0;
        if (!matchGuardedReductions(vp, maskp, bits) || bits != maskp->width()) continue;
        FileLine* const flp = vp->fileline();
        auto* const activep = new DfgRedOr{graph, flp, DfgVertex::dtypeForWidth(1)};
        activep->srcp(maskp);
        auto* const cp = new DfgCond{graph, flp, vp->dtypep()};
        cp->condp(activep);
        cp->elsep(new DfgConst{graph, flp, bits, 0});
        vp->replaceWith(cp);
        cp->thenp(vp);
        ++count;
    }
    return count;
}

// Match one driver at its actual destination offset (which need not be
// aligned to a column). The only source accepted is an undriven input port.
static bool matchTranspose(DfgVertex* vp, unsigned side, unsigned pos, DfgVarPacked*& inputp) {
    if (vp->hasMultipleSinks()) return false;
    if (auto* const cp = vp->cast<DfgConcat>()) {
        return matchTranspose(cp->rhsp(), side, pos, inputp)
               && matchTranspose(cp->lhsp(), side, pos + cp->rhsp()->width(), inputp);
    }
    auto* const sp = vp->cast<DfgSel>();
    if (!sp || sp->width() != 1 || sp->lsb() != (pos % side) * side + pos / side) return false;
    auto* const srcp = sp->fromp()->cast<DfgVarPacked>();
    if (!srcp || srcp->width() != side * side || srcp->isDrivenByDfg()
        || srcp->varp()->direction() != VDirection::INPUT || srcp->varp()->isSc()
        || srcp->varp()->user3()) {
        return false;
    }
    if (!inputp) inputp = srcp;
    return inputp == srcp;
}

static unsigned fuseTransposeReductions(DfgGraph& graph) {
    unsigned count = 0;
    for (auto* vv = graph.varVerticesBeginp(); vv; vv = vv->verticesNext()) {
        auto* const tmp = vv->cast<DfgVarPacked>();
        if (!tmp || !tmp->isDrivenByDfg() || tmp->keep() || tmp->hasRefs()
            || tmp->varp()->isSc() || tmp->width() < 64 || tmp->width() > 4096) continue;
        auto* const first = tmp->findSink<DfgSel>();
        if (!first) continue;
        const unsigned n = first->width();
        if (n < 8 || n > 64 || n*n != tmp->width() || tmp->fanout() != n) continue;

        DfgVarPacked* maskp = nullptr;
        std::vector<DfgRedOr*> reductions(n, nullptr);
        tmp->forEachSink([&](DfgVertex& sink) {
            auto* const s = sink.cast<DfgSel>();
            if (!s || s->width() != n || s->lsb() % n || s->lsb()/n >= n
                || s->hasMultipleSinks()) return;
            auto* const a = s->findSink<DfgAnd>();
            if (!a || a->hasMultipleSinks()) return;
            auto* const m = (a->lhsp() == s ? a->rhsp() : a->lhsp())->cast<DfgVarPacked>();
            auto* const r = a->findSink<DfgRedOr>();
            if (!r || !m || m->width() != n || m->varp()->isSc() || (maskp && m != maskp)) return;
            maskp = m;
            reductions[s->lsb()/n] = r;
        });
        if (std::find(reductions.begin(), reductions.end(), nullptr) != reductions.end()) continue;
        std::vector<bool> covered(n*n);
        DfgVarPacked* inputp = nullptr;
        bool ok = true;
        for (size_t i = 0; ok && i < tmp->arity(); ++i) {
            auto* const driver = tmp->source(i);
            const unsigned start = tmp->driverLsb(i);
            if (!driver || start >= covered.size() || driver->width() > covered.size()-start
                || !matchTranspose(driver, n, start, inputp)) {
                ok = false;
                break;
            }
            for (unsigned b = start; b < start + driver->width(); ++b) {
                if (covered[b]) ok = false;
                covered[b] = true;
            }
        }
        if (!ok || std::find(covered.begin(), covered.end(), false) != covered.end()) continue;

        FileLine* const fl = tmp->fileline();
        auto* const bit = DfgVertex::dtypeForWidth(1);
        auto* const word = maskp->dtypep();
        const auto sel = [&](DfgVertex* from, unsigned lsb, AstNodeDType* dt) {
            auto* const sp = new DfgSel{graph, fl, dt};
            sp->fromp(from);
            sp->lsb(lsb);
            return sp;
        };
        // OR whole rows selected by mask[r]. Sharing this one vector across
        // all columns avoids building the original transposed storage at all.
        std::vector<DfgVertex*> terms;
        for (unsigned r = 0; r < n; ++r) {
            auto* const broadcast = new DfgExtendS{graph, fl, word};
            broadcast->srcp(sel(maskp, r, bit));
            auto* const term = new DfgAnd{graph, fl, word};
            term->lhsp(broadcast);
            term->rhsp(sel(inputp, r*n, word));
            terms.push_back(term);
        }
        while (terms.size() > 1) {
            size_t dst = 0;
            for (size_t i = 0; i < terms.size(); i += 2) {
                DfgVertex* p = terms[i];
                if (i+1 < terms.size()) {
                    auto* const both = new DfgOr{graph, fl, word};
                    both->lhsp(p);
                    both->rhsp(terms[i+1]);
                    p = both;
                }
                terms[dst++] = p;
            }
            terms.resize(dst);
        }
        auto* const active = new DfgRedOr{graph, fl, bit};
        active->srcp(maskp);
        auto* const result = new DfgCond{graph, fl, word};
        result->condp(active);
        result->thenp(terms.front());
        result->elsep(new DfgConst{graph, fl, n, 0});
        for (unsigned c = 0; c < n; ++c) {
            reductions[c]->replaceWith(sel(result, c, bit));
            reductions[c]->unlinkDelete(graph);
        }
        ++count;
    }
    return count;
}
}  // namespace

// Independent of thread partitioning. IDs are local to this snapshot, not
// addresses or promises that an expression survives subsequent DFG passes.
static void dumpSentinelDfg(const DfgGraph& graph, const string& phase) {
    const string filename = v3Global.debugFilename("sentinel_dfg") + ".json";
    const std::unique_ptr<std::ofstream> osp{V3File::new_ofstream(filename)};
    if (osp->fail()) v3fatal("Can't write " << filename);
    const auto quote = [](const string& s) {
        string result = "\"";
        static constexpr char hex[] = "0123456789abcdef";
        for (const unsigned char c : s) {
            if (c < 32) {
                result += "\\u00";
                result += hex[c >> 4];
                result += hex[c & 15];
            } else {
                if (c == '"' || c == '\\') result += '\\';
                result += c;
            }
        }
        return result + '"';
    };
    std::unordered_map<const DfgVertex*, size_t> ids;
    graph.forEachVertex([&](const DfgVertex& v) { ids.emplace(&v, ids.size()); });
    *osp << "{\"schema\":\"v3-sentinel-dfg-1\",\"module\":" << quote(graph.modulep()->name())
         << ",\"phase\":" << quote(phase) << ",\"vertices\":[";
    bool first = true;
    graph.forEachVertex([&](const DfgVertex& v) {
        *osp << (first ? "\n" : ",\n") << "{\"id\":" << ids.at(&v)
             << ",\"op\":" << quote(v.typeName()) << ",\"file\":" << quote(v.fileline()->filename())
             << ",\"line\":" << v.fileline()->lineno();
        first = false;
        if (VN_IS(v.dtypep(), BasicDType)) *osp << ",\"bits\":" << v.width();
        if (const auto* const selp = v.cast<DfgSel>()) *osp << ",\"lsb\":" << selp->lsb();
        if (const auto* const varp = v.cast<DfgVertexVar>()) {
            *osp << ",\"name\":" << quote(varp->varp()->name())
                 << ",\"keep\":" << (varp->keep() ? "true" : "false")
                 << ",\"module_refs\":" << (varp->hasModRefs() ? "true" : "false")
                 << ",\"external_refs\":" << (varp->hasExtRefs() ? "true" : "false");
        }
        *osp << ",\"inputs\":[";
        bool firstInput = true;
        v.forEachSourceEdge([&](const DfgEdge& e, size_t slot) {
            if (!e.sourcep()) return;
            *osp << (firstInput ? "" : ",") << "[" << slot << "," << ids.at(e.sourcep());
            if (const auto* const varp = v.cast<DfgVarPacked>()) {
                *osp << "," << varp->driverLsb(slot);
            } else if (const auto* const arrayp = v.cast<DfgVarArray>()) {
                *osp << "," << arrayp->driverIndex(slot);
            }
            *osp << "]";
            firstInput = false;
        });
        *osp << "]}";
    });
    *osp << "\n]}\n";
    osp->close();
    if (osp->fail()) v3fatal("Can't finish writing " << filename);
}

// Extract more combinational logic equations from procedures for better optimization opportunities
class DataflowExtractVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user3            -> bool: Flag indicating variable is subject of force or release
    // statement AstVar::user4  -> bool: Flag indicating variable is combinationally driven
    // AstNodeModule::user4     -> Extraction candidates (via m_extractionCandidates)
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;

    // Expressions considered for extraction as separate assignment to gain more opportunities for
    // optimization, together with the list of variables they read.
    using Candidates = std::vector<std::pair<AstNodeExpr*, std::vector<const AstVar*>>>;

    // Expressions considered for extraction. All the candidates are pure expressions.
    AstUser4Allocator<AstNodeModule, Candidates> m_extractionCandidates;

    // STATE
    AstNodeModule* m_modp = nullptr;  // The module being visited
    Candidates* m_candidatesp = nullptr;
    bool m_impure = false;  // True if the visited tree has a side effect
    bool m_inForceReleaseLhs = false;  // Iterating LHS of force/release
    // List of AstVar nodes read by the visited tree. 'vector' rather than 'set' as duplicates are
    // somewhat unlikely and we can handle them later.
    std::vector<const AstVar*> m_readVars;

    // METHODS

    // Node considered for extraction as a combinational equation. Trace variable usage/purity.
    void iterateExtractionCandidate(AstNode* nodep) {
        UASSERT_OBJ(!VN_IS(nodep->backp(), NodeExpr), nodep,
                    "Should not try to extract nested expressions (only root expressions)");

        // Simple VarRefs should not be extracted, as they only yield trivial assignments.
        // Similarly, don't extract anything if no candidate map is set up (for non-modules).
        // We still need to visit them though, to mark hierarchical references.
        if (VN_IS(nodep, NodeVarRef) || !m_candidatesp) {
            iterate(nodep);
            return;
        }

        // Don't extract plain constants
        if (VN_IS(nodep, Const)) return;

        // Candidates can't nest, so no need for VL_RESTORER, just initialize iteration state
        m_impure = false;
        m_readVars.clear();

        // Trace variable usage
        iterate(nodep);

        // We only extract pure expressions
        if (m_impure) return;

        // Do not extract expressions without any variable references
        if (m_readVars.empty()) return;

        // Add to candidate list
        m_candidatesp->emplace_back(VN_AS(nodep, NodeExpr), std::move(m_readVars));
    }

    // VISIT methods

    void visit(AstNetlist* nodep) override {
        // Analyse the whole design
        iterateChildrenConst(nodep);

        // Replace candidate expressions only reading combinationally driven signals with variables
        V3UniqueNames names{"__VdfgExtracted"};
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            // Only extract from proper modules
            if (!VN_IS(modp, Module)) continue;

            for (const auto& pair : m_extractionCandidates(modp)) {
                AstNodeExpr* const cnodep = pair.first;

                // Do not extract expressions without any variable references
                if (pair.second.empty()) continue;

                // Check if all variables read by this expression are driven combinationally,
                // and move on if not. Also don't extract it if one of the variables is subject
                // to a force/release, as releasing nets must have immediate effect, but adding
                // extra combinational logic can change semantics (see t_force_release_net*).
                {
                    bool hasBadVar = false;
                    for (const AstVar* const readVarp : pair.second) {
                        // variable is target of force/release or not combinationally driven
                        if (readVarp->user3() || !readVarp->user4()) {
                            hasBadVar = true;
                            break;
                        }
                    }
                    if (hasBadVar) continue;
                }

                // Create temporary variable
                FileLine* const flp = cnodep->fileline();
                const string name = names.get(cnodep);
                AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, cnodep->dtypep()};
                varp->trace(false);
                modp->addStmtsp(varp);

                // Replace expression with temporary variable
                cnodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});

                // Add assignment driving temporary variable
                modp->addStmtsp(
                    new AstAssignW{flp, new AstVarRef{flp, varp, VAccess::WRITE}, cnodep});
            }
        }
    }

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }

    void visit(AstAlways* nodep) override {
        VL_RESTORER(m_candidatesp);
        // Only extract from combinational logic under proper modules
        const bool isComb = !nodep->sensesp()
                            && (nodep->keyword() == VAlwaysKwd::ALWAYS
                                || nodep->keyword() == VAlwaysKwd::ALWAYS_COMB
                                || nodep->keyword() == VAlwaysKwd::ALWAYS_LATCH);
        m_candidatesp
            = isComb && VN_IS(m_modp, Module) ? &m_extractionCandidates(m_modp) : nullptr;
        iterateChildrenConst(nodep);
    }

    void visit(AstAssignW* nodep) override {
        // Mark LHS variable as combinationally driven
        if (AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef)) vrefp->varp()->user4(true);
        //
        iterateChildrenConst(nodep);
    }

    void visit(AstAssign* nodep) override {
        iterateExtractionCandidate(nodep->rhsp());
        iterate(nodep->lhsp());
    }

    void visit(AstAssignDly* nodep) override {
        iterateExtractionCandidate(nodep->rhsp());
        iterate(nodep->lhsp());
    }

    void visit(AstIf* nodep) override {
        iterateExtractionCandidate(nodep->condp());
        iterateAndNextConstNull(nodep->thensp());
        iterateAndNextConstNull(nodep->elsesp());
    }

    void visit(AstAssignForce* nodep) override {
        VL_RESTORER(m_inForceReleaseLhs);
        iterate(nodep->rhsp());
        UASSERT_OBJ(!m_inForceReleaseLhs, nodep, "Should not nest");
        m_inForceReleaseLhs = true;
        iterate(nodep->lhsp());
    }

    void visit(AstRelease* nodep) override {
        VL_RESTORER(m_inForceReleaseLhs);
        UASSERT_OBJ(!m_inForceReleaseLhs, nodep, "Should not nest");
        m_inForceReleaseLhs = true;
        iterate(nodep->lhsp());
    }

    void visit(AstNodeExpr* nodep) override { iterateChildrenConst(nodep); }

    void visit(AstNodeVarRef* nodep) override {
        if (nodep->access().isWriteOrRW()) {
            // If it writes a variable, mark as impure
            m_impure = true;
            // Mark target of force/release
            if (m_inForceReleaseLhs) nodep->varp()->user3(true);
        } else {
            // Otherwise, add read reference
            m_readVars.push_back(nodep->varp());
        }
    }

    void visit(AstNode* nodep) override {
        // Conservatively assume unhandled nodes are impure. This covers all AstNodeFTaskRef
        // as AstNodeFTaskRef are sadly not AstNodeExpr.
        m_impure = true;
        // Still need to gather all references/force/release, etc.
        iterateChildrenConst(nodep);
    }

    // CONSTRUCTOR
    explicit DataflowExtractVisitor(AstNetlist* netlistp) { iterate(netlistp); }

public:
    static void apply(AstNetlist* netlistp) { DataflowExtractVisitor{netlistp}; }
};

void V3DfgOptimizer::extract(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Extract more optimization candidates
    DataflowExtractVisitor::apply(netlistp);
    V3Global::dumpCheckGlobalTree("dfg-extract", 0, dumpTree() >= 3);
}

void V3DfgOptimizer::optimize(AstNetlist* netlistp, const string& label) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    // NODE STATE
    // AstVar::user1 -> Used by V3DfgPasses::astToDfg and DfgPassed::dfgToAst
    // AstVar::user2 -> bool: Flag indicating referenced by AstVarXRef (set just below)
    // AstVar::user3 -> bool: Flag indicating written by logic not representable as DFG
    //                        (set by V3DfgPasses::astToDfg)
    const VNUser2InUse user2InUse;
    const VNUser3InUse user3InUse;

    // Mark cross-referenced variables
    netlistp->foreach([](const AstVarXRef* xrefp) { xrefp->varp()->user2(true); });

    V3DfgOptimizationContext ctx{label};
    const bool packPlanes = v3Global.constRemoveXs() && v3Global.opt.fDfgPeephole()
                            && v3Global.opt.fDfgPeepholeEnabled("pack-byte-plane");
    uint64_t planes = 0;
    const bool packPreds = v3Global.constRemoveXs() && v3Global.opt.fDfgPeephole()
                           && v3Global.opt.fDfgPeepholeEnabled("pack-predicates");
    uint64_t predicates = 0;
    const bool packMux = v3Global.constRemoveXs() && v3Global.opt.fDfgPeephole()
                         && v3Global.opt.fDfgPeepholeEnabled("pack-bitwise-mux");
    uint64_t muxes = 0;
    const bool guardMasks = v3Global.constRemoveXs() && v3Global.opt.fDfgPeephole()
                            && v3Global.opt.fDfgPeepholeEnabled("guard-empty-mask");
    uint64_t guarded = 0;
    const bool fuseRows = v3Global.constRemoveXs() && v3Global.opt.fDfgPeephole()
                          && v3Global.opt.fDfgPeepholeEnabled("fuse-transpose-reductions");
    uint64_t fused = 0;

    // Run the optimization phase
    for (AstNode* nodep = netlistp->modulesp(); nodep; nodep = nodep->nextp()) {
        // Only optimize proper modules
        AstModule* const modp = VN_CAST(nodep, Module);
        if (!modp) continue;

        UINFO(4, "Applying DFG optimization to module '" << modp->name() << "'" << endl);
        ++ctx.m_modules;

        // Build the DFG of this module
        const std::unique_ptr<DfgGraph> dfg{V3DfgPasses::astToDfg(*modp, ctx)};
        if (v3Global.opt.dumpLevel("sentinel")) dumpSentinelDfg(*dfg, label);
        if (dumpDfg() >= 8) dfg->dumpDotFilePrefixed(ctx.prefix() + "whole-input");

        // Extract the cyclic sub-graphs. We do this because a lot of the optimizations assume a
        // DAG, and large, mostly acyclic graphs could not be optimized due to the presence of
        // small cycles.
        const std::vector<std::unique_ptr<DfgGraph>>& cyclicComponents
            = dfg->extractCyclicComponents("cyclic");

        // Split the remaining acyclic DFG into [weakly] connected components
        const std::vector<std::unique_ptr<DfgGraph>>& acyclicComponents
            = dfg->splitIntoComponents("acyclic");

        // Quick sanity check
        UASSERT_OBJ(dfg->size() == 0, nodep, "DfgGraph should have become empty");

        // For each cyclic component
        for (auto& component : cyclicComponents) {
            if (dumpDfg() >= 7) component->dumpDotFilePrefixed(ctx.prefix() + "source");
            // TODO: Apply optimizations safe for cyclic graphs
            // Add back under the main DFG (we will convert everything back in one go)
            dfg->addGraph(*component);
        }

        // For each acyclic component
        for (auto& component : acyclicComponents) {
            if (dumpDfg() >= 7) component->dumpDotFilePrefixed(ctx.prefix() + "source");
            // Optimize the component
            if (fuseRows) fused += fuseTransposeReductions(*component);
            if (packPlanes) planes += packBytePlanes(*component);
            if (packPreds) predicates += packPredicates(*component);
            if (packMux) muxes += packBitwiseMux(*component);
            if (guardMasks) guarded += guardEmptyMasks(*component);
            V3DfgPasses::optimize(*component, ctx);
            // Add back under the main DFG (we will convert everything back in one go)
            dfg->addGraph(*component);
        }

        // Convert back to Ast
        if (dumpDfg() >= 8) dfg->dumpDotFilePrefixed(ctx.prefix() + "whole-optimized");
        AstModule* const resultModp = V3DfgPasses::dfgToAst(*dfg, ctx);
        UASSERT_OBJ(resultModp == modp, modp, "Should be the same module");
    }
    if (packPlanes) V3Stats::addStat("Optimizations, DFG " + label + " packed byte planes", planes);
    if (packPreds) {
        V3Stats::addStat("Optimizations, DFG " + label + " packed predicates", predicates);
    }
    if (packMux) {
        V3Stats::addStat("Optimizations, DFG " + label + " packed bitwise muxes", muxes);
    }
    if (guardMasks) V3Stats::addStat("Optimizations, DFG " + label + " empty mask guards", guarded);
    if (fuseRows) V3Stats::addStat("Optimizations, DFG " + label + " fused transposes", fused);
    V3Global::dumpCheckGlobalTree("dfg-optimize", 0, dumpTree() >= 3);
}
