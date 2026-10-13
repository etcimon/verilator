// DESCRIPTION: Verilator: wide-word SIMD kernels against the scalar reference
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <cstdio>
#include <cstring>
#include <vector>

// Outside the test driver (plain `verilator --cc --exe --build --top-module t`)
// the prefix defaults to Vt.
#ifndef VM_PREFIX
#define VM_PREFIX Vt
#endif
#ifndef VM_PREFIX_INCLUDE
#define VM_PREFIX_INCLUDE "Vt.h"
#endif
#include VM_PREFIX_INCLUDE

double sc_time_stamp() { return 0; }

// Scalar reference: the word loops as they were before the SIMD kernels, with
// the same bounds handling. Any divergence is a kernel bug, not a spec question.
namespace ref {
static void assign(int obits, EData* o, const EData* l) {
    for (int i = 0; i < VL_WORDS_I(obits); ++i) o[i] = l[i];
}
static void extend(int obits, int lbits, EData* o, const EData* l) {
    for (int i = 0; i < VL_WORDS_I(lbits); ++i) o[i] = l[i];
    for (int i = VL_WORDS_I(lbits); i < VL_WORDS_I(obits); ++i) o[i] = 0;
}
static void and_(int w, EData* o, const EData* l, const EData* r) {
    for (int i = 0; i < w; ++i) o[i] = l[i] & r[i];
}
static void or_(int w, EData* o, const EData* l, const EData* r) {
    for (int i = 0; i < w; ++i) o[i] = l[i] | r[i];
}
static void xor_(int w, EData* o, const EData* l, const EData* r) {
    for (int i = 0; i < w; ++i) o[i] = l[i] ^ r[i];
}
static void not_(int w, EData* o, const EData* l) {
    for (int i = 0; i < w; ++i) o[i] = ~l[i];
}
static IData eq(int w, const EData* l, const EData* r) {
    EData n = 0;
    for (int i = 0; i < w; ++i) n |= l[i] ^ r[i];
    return n == 0;
}
static IData changexor(int w, const EData* l, const EData* r) {
    IData n = 0;
    for (int i = 0; i < w; ++i) n |= l[i] ^ r[i];
    return n;
}
static IData redor(int w, const EData* l) {
    EData n = 0;
    for (int i = 0; i < w; ++i) n |= l[i];
    return n != 0;
}
static void insert_ww(EData* iowp, const EData* lwp, int hbit, int lbit, int rbits) {
    if (rbits > 0 && hbit >= rbits) {
        if (lbit >= rbits) return;
        hbit = rbits - 1;
    }
    const int hoffset = VL_BITBIT_E(hbit);
    const int loffset = VL_BITBIT_E(lbit);
    const int roffset = VL_BITBIT_E(rbits);
    const int lword = VL_BITWORD_E(lbit);
    const int hword = VL_BITWORD_E(hbit);
    const int rword = VL_BITWORD_E(rbits);
    const int words = VL_WORDS_I(hbit - lbit + 1);
    const EData cleanmask = hword == rword ? VL_MASK_E(roffset) : VL_MASK_E(0);
    if (hoffset == VL_SIZEBITS_E && loffset == 0) {
        for (int i = 0; i < (words - 1); ++i) iowp[lword + i] = lwp[i];
        iowp[hword] = lwp[words - 1] & cleanmask;
    } else if (loffset == 0) {
        for (int i = 0; i < (words - 1); ++i) iowp[lword + i] = lwp[i];
        const EData hinsmask = (VL_MASK_E(hoffset - 0 + 1));
        iowp[hword] = (iowp[hword] & ~hinsmask) | (lwp[words - 1] & (hinsmask & cleanmask));
    } else {
        const EData hinsmask = (VL_MASK_E(hoffset - 0 + 1)) << 0;
        const EData linsmask = (VL_MASK_E((VL_EDATASIZE - 1) - loffset + 1)) << loffset;
        const int nbitsonright = VL_EDATASIZE - loffset;
        for (int i = 0; i < words; ++i) {
            {
                const int oword = lword + i;
                const EData d = lwp[i] << loffset;
                const EData od = (iowp[oword] & ~linsmask) | (d & linsmask);
                if (oword == hword) {
                    iowp[oword] = (iowp[oword] & ~hinsmask) | (od & (hinsmask & cleanmask));
                } else {
                    iowp[oword] = od;
                }
            }
            {
                const int oword = lword + i + 1;
                if (oword <= hword) {
                    const EData d = lwp[i] >> nbitsonright;
                    const EData od = (d & ~linsmask) | (iowp[oword] & linsmask);
                    if (oword == hword) {
                        iowp[oword] = (iowp[oword] & ~hinsmask) | (od & (hinsmask & cleanmask));
                    } else {
                        iowp[oword] = od;
                    }
                }
            }
        }
    }
}
static void shiftl(int obits, EData* owp, const EData* lwp, IData rd) {
    const int word_shift = VL_BITWORD_E(rd);
    const int bit_shift = VL_BITBIT_E(rd);
    if (rd >= static_cast<IData>(obits)) {
        for (int i = 0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    } else if (bit_shift == 0) {
        for (int i = 0; i < word_shift; ++i) owp[i] = 0;
        for (int i = word_shift; i < VL_WORDS_I(obits); ++i) owp[i] = lwp[i - word_shift];
    } else {
        for (int i = 0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
        insert_ww(owp, lwp, obits - 1, rd, 0);
    }
}
static void shiftr(int obits, EData* owp, const EData* lwp, IData rd) {
    const int word_shift = VL_BITWORD_E(rd);
    const int bit_shift = VL_BITBIT_E(rd);
    if (rd >= static_cast<IData>(obits)) {
        for (int i = 0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    } else if (bit_shift == 0) {
        const int copy_words = (VL_WORDS_I(obits) - word_shift);
        for (int i = 0; i < copy_words; ++i) owp[i] = lwp[i + word_shift];
        for (int i = copy_words; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    } else {
        const int loffset = rd & VL_SIZEBITS_E;
        const int nbitsonright = VL_EDATASIZE - loffset;
        const int words = VL_WORDS_I(obits - rd);
        for (int i = 0; i < words; ++i) {
            owp[i] = lwp[i + word_shift] >> loffset;
            const int upperword = i + word_shift + 1;
            if (upperword < VL_WORDS_I(obits)) owp[i] |= lwp[upperword] << nbitsonright;
        }
        for (int i = words; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    }
}
static void extends(int obits, int lbits, EData* owp, const EData* lwp) {
    for (int i = 0; i < VL_WORDS_I(lbits) - 1; ++i) owp[i] = lwp[i];
    const int lmsw = VL_WORDS_I(lbits) - 1;
    const EData sign = VL_SIGNONES_E(lbits, lwp[lmsw]);
    owp[lmsw] = lwp[lmsw] | (sign & ~VL_MASK_E(lbits));
    for (int i = VL_WORDS_I(lbits); i < VL_WORDS_I(obits); ++i) owp[i] = sign;
}
static void shiftrs(int obits, int lbits, EData* owp, const EData* lwp, IData rd) {
    const int word_shift = VL_BITWORD_E(rd);
    const int bit_shift = VL_BITBIT_E(rd);
    const int lmsw = VL_WORDS_I(obits) - 1;
    const EData sign = VL_SIGNONES_E(lbits, lwp[lmsw]);
    if (rd >= static_cast<IData>(obits)) {
        for (int i = 0; i <= lmsw; ++i) owp[i] = sign;
        owp[lmsw] &= VL_MASK_E(lbits);
    } else if (bit_shift == 0) {
        const int copy_words = (VL_WORDS_I(obits) - word_shift);
        for (int i = 0; i < copy_words; ++i) owp[i] = lwp[i + word_shift];
        if (copy_words >= 0) owp[copy_words - 1] |= ~VL_MASK_E(obits) & sign;
        for (int i = copy_words; i < VL_WORDS_I(obits); ++i) owp[i] = sign;
        owp[lmsw] &= VL_MASK_E(lbits);
    } else {
        const int loffset = rd & VL_SIZEBITS_E;
        const int nbitsonright = VL_EDATASIZE - loffset;
        const int words = VL_WORDS_I(obits - rd);
        for (int i = 0; i < words; ++i) {
            owp[i] = lwp[i + word_shift] >> loffset;
            const int upperword = i + word_shift + 1;
            if (upperword < VL_WORDS_I(obits)) owp[i] |= lwp[upperword] << nbitsonright;
        }
        if (words) owp[words - 1] |= sign & ~VL_MASK_E(obits - loffset);
        for (int i = words; i < VL_WORDS_I(obits); ++i) owp[i] = sign;
        owp[lmsw] &= VL_MASK_E(lbits);
    }
}
static IData redxor(int w, const EData* l) {
    EData r = l[0];
    for (int i = 1; i < w; ++i) r ^= l[i];
    r = (r ^ (r >> 1));
    r = (r ^ (r >> 2));
    r = (r ^ (r >> 4));
    r = (r ^ (r >> 8));
    r = (r ^ (r >> 16));
    return r & 1;
}
static IData countones(int w, const EData* l) {
    IData r = 0;
    for (int i = 0; i < w; ++i)
        for (int b = 0; b < 32; ++b) r += (l[i] >> b) & 1;
    return r;
}
static void sel(int obits, int lbits, EData* owp, const EData* lwp, IData lsb, IData width) {
    const int msb = lsb + width - 1;
    const int word_shift = VL_BITWORD_E(lsb);
    if (msb > lbits) {
        for (int i = 0; i < VL_WORDS_I(obits) - 1; ++i) owp[i] = ~0;
        owp[VL_WORDS_I(obits) - 1] = VL_MASK_E(obits);
    } else if (VL_BITBIT_E(lsb) == 0) {
        for (int i = 0; i < VL_WORDS_I(obits); ++i) owp[i] = lwp[i + word_shift];
    } else {
        const int loffset = lsb & VL_SIZEBITS_E;
        const int nbitsfromlow = VL_EDATASIZE - loffset;
        const int words = VL_WORDS_I(msb - lsb + 1);
        for (int i = 0; i < words; ++i) {
            owp[i] = lwp[i + word_shift] >> loffset;
            const int upperword = i + word_shift + 1;
            if (upperword <= static_cast<int>(VL_BITWORD_E(msb))) {
                owp[i] |= lwp[upperword] << nbitsfromlow;
            }
        }
        for (int i = words; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    }
}
}  // namespace ref

static uint64_t g_rng = 0x9e3779b97f4a7c15ULL;
static EData rnd() {
    g_rng ^= g_rng << 13;
    g_rng ^= g_rng >> 7;
    g_rng ^= g_rng << 17;
    return static_cast<EData>(g_rng);
}
static void fill(std::vector<EData>& v) {
    for (auto& w : v) w = rnd();
}
static int g_fail = 0;
static void check(bool ok, const char* what, int a, int b, int c) {
    if (!ok && g_fail++ < 20) printf("%%Error: simd wide mismatch %s %d %d %d\n", what, a, b, c);
}

static void testWords(int words) {
    const int obits = words * 32 - static_cast<int>(rnd() % 32);
    std::vector<EData> l(words + 4), r(words + 4), o1(words + 4), o2(words + 4);
    fill(l);
    fill(r);
    // Elementwise, including in-place aliasing (o == l).
    for (int alias = 0; alias < 2; ++alias) {
        std::vector<EData> a = l, b = l;
        EData* o1p = alias ? a.data() : o1.data();
        EData* o2p = alias ? b.data() : o2.data();
        VL_AND_W(words, o1p, alias ? a.data() : l.data(), r.data());
        ref::and_(words, o2p, alias ? b.data() : l.data(), r.data());
        check(std::memcmp(o1p, o2p, words * 4) == 0, "and", words, alias, 0);
        a = l; b = l;
        VL_OR_W(words, o1p, alias ? a.data() : l.data(), r.data());
        ref::or_(words, o2p, alias ? b.data() : l.data(), r.data());
        check(std::memcmp(o1p, o2p, words * 4) == 0, "or", words, alias, 0);
        a = l; b = l;
        VL_XOR_W(words, o1p, alias ? a.data() : l.data(), r.data());
        ref::xor_(words, o2p, alias ? b.data() : l.data(), r.data());
        check(std::memcmp(o1p, o2p, words * 4) == 0, "xor", words, alias, 0);
        a = l; b = l;
        VL_NOT_W(words, o1p, alias ? a.data() : l.data());
        ref::not_(words, o2p, alias ? b.data() : l.data());
        check(std::memcmp(o1p, o2p, words * 4) == 0, "not", words, alias, 0);
    }
    VL_ASSIGN_W(obits, o1.data(), l.data());
    ref::assign(obits, o2.data(), l.data());
    check(std::memcmp(o1.data(), o2.data(), words * 4) == 0, "assign", words, 0, 0);
    // Equality: equal, differing in one word, differing in the last word.
    std::vector<EData> e = l;
    check(VL_EQ_W(words, l.data(), e.data()) == ref::eq(words, l.data(), e.data()), "eq", words, 0, 0);
    check(VL_CHANGEXOR_W(words, l.data(), r.data()) == ref::changexor(words, l.data(), r.data()),
          "changexor", words, 0, 0);
    for (int k = 0; k < words; ++k) {
        e = l;
        e[k] ^= 1U << (rnd() % 32);
        check(VL_EQ_W(words, l.data(), e.data()) == ref::eq(words, l.data(), e.data()), "eq-k", words, k, 0);
        check(VL_CHANGEXOR_W(words, l.data(), e.data()) == ref::changexor(words, l.data(), e.data()),
              "changexor-k", words, k, 0);
        std::vector<EData> z(words, 0);
        z[k] = 1U << (rnd() % 32);
        check(VL_REDOR_W(words, z.data()) == ref::redor(words, z.data()), "redor", words, k, 0);
    }
    std::vector<EData> z(words, 0);
    check(VL_REDOR_W(words, z.data()) == ref::redor(words, z.data()), "redor0", words, 0, 0);
    // Extend into a wider destination.
    {
        const int owords = words + 1 + static_cast<int>(rnd() % 3);
        std::vector<EData> x1(owords), x2(owords);
        VL_EXTEND_WW(owords * 32, obits, x1.data(), l.data());
        ref::extend(owords * 32, obits, x2.data(), l.data());
        check(std::memcmp(x1.data(), x2.data(), owords * 4) == 0, "extend", words, owords, 0);
    }
    // Reductions and signed extension.
    check((VL_REDXOR_W(words, l.data()) & 1) == ref::redxor(words, l.data()), "redxor", words, 0, 0);
    check(VL_COUNTONES_W(words, l.data()) == ref::countones(words, l.data()), "countones", words, 0, 0);
    check(VL_COUNTONES_Q((static_cast<QData>(l[0]) << 32) | r[0])
              == ref::countones(1, &l[0]) + ref::countones(1, &r[0]),
          "countones_q", words, 0, 0);
    {
        const int owords = words + 1 + static_cast<int>(rnd() % 3);
        std::vector<EData> x1(owords), x2(owords), lc = l;
        lc[words - 1] &= VL_MASK_E(obits);  // clean operand as the emitter guarantees
        for (int sign = 0; sign < 2; ++sign) {
            if (sign) lc[words - 1] |= 1U << ((obits - 1) % 32);
            else lc[words - 1] &= ~(1U << ((obits - 1) % 32));
            VL_EXTENDS_WW(owords * 32, obits, x1.data(), lc.data());
            ref::extends(owords * 32, obits, x2.data(), lc.data());
            check(std::memcmp(x1.data(), x2.data(), owords * 4) == 0, "extends", words, owords, sign);
        }
        VL_COND_WIWW(obits, o1.data(), 1, l.data(), r.data());
        check(std::memcmp(o1.data(), l.data(), words * 4) == 0, "cond1", words, 0, 0);
        VL_COND_WIWW(obits, o1.data(), 0, l.data(), r.data());
        check(std::memcmp(o1.data(), r.data(), words * 4) == 0, "cond0", words, 0, 0);
    }
    // Shifts by every amount, select of every (lsb, width) pair on a stride.
    for (IData rd = 0; rd <= static_cast<IData>(obits) + 1; rd += 1 + (rd % 7)) {
        VL_SHIFTL_WWI(obits, obits, 32, o1.data(), l.data(), rd);
        ref::shiftl(obits, o2.data(), l.data(), rd);
        check(std::memcmp(o1.data(), o2.data(), words * 4) == 0, "shiftl", obits, rd, 0);
        VL_SHIFTR_WWI(obits, obits, 32, o1.data(), l.data(), rd);
        ref::shiftr(obits, o2.data(), l.data(), rd);
        check(std::memcmp(o1.data(), o2.data(), words * 4) == 0, "shiftr", obits, rd, 0);
        std::vector<EData> lc = l;
        lc[words - 1] &= VL_MASK_E(obits);
        for (int sign = 0; sign < 2; ++sign) {
            if (sign) lc[words - 1] |= 1U << ((obits - 1) % 32);
            VL_SHIFTRS_WWI(obits, obits, 32, o1.data(), lc.data(), rd);
            ref::shiftrs(obits, obits, o2.data(), lc.data(), rd);
            check(std::memcmp(o1.data(), o2.data(), words * 4) == 0, "shiftrs", obits, rd, sign);
        }
    }
    // Trigger vector word operations and the word-mask guard against the bit tests.
    {
        VlTriggerVec<324> a, b, c;
        for (int k = 0; k < 324; k += 1 + static_cast<int>(rnd() % 9)) a.at(k) = true;
        for (int k = 0; k < 324; k += 1 + static_cast<int>(rnd() % 5)) b.at(k) = true;
        bool anyRef = false;
        for (int k = 0; k < 324; ++k) anyRef |= a.at(k);
        check(a.any() == anyRef, "trig-any", words, 0, 0);
        c.andNot(a, b);
        for (int k = 0; k < 324; ++k) {
            check(c.at(k) == (a.at(k) && !b.at(k)), "trig-andnot", words, k, 0);
        }
        c.set(b);
        for (int k = 0; k < 324; ++k) {
            check(c.at(k) == ((a.at(k) && !b.at(k)) || b.at(k)), "trig-set", words, k, 0);
        }
        for (int w = 0; w < 6; ++w) {
            const uint64_t mask = (static_cast<uint64_t>(rnd()) << 32) | rnd();
            bool bitsRef = false;
            for (int bit = 0; bit < 64 && w * 64 + bit < 324; ++bit) {
                if (mask >> bit & 1) bitsRef |= a.at(w * 64 + bit);
            }
            check(a.wordAny(w, mask) == bitsRef, "trig-wordany", words, w, 0);
        }
        VlTriggerVec<1> one;
        check(!one.any(), "trig-one-empty", words, 0, 0);
        one.at(0) = true;
        check(one.any() && one.wordAny(0, 1), "trig-one-set", words, 0, 0);
    }
    // VlWide / VlUnpacked change detection.
    {
        VlWide<7> wa, wb;
        for (int k = 0; k < 7; ++k) wa[k] = wb[k] = rnd();
        check(!(wa != wb), "vlwide-eq", words, 0, 0);
        wb[rnd() % 7] ^= 1U << (rnd() % 32);
        check(wa != wb, "vlwide-neq", words, 0, 0);
        VlUnpacked<CData, 5> ua, ub;
        for (int k = 0; k < 5; ++k) ua[k] = ub[k] = static_cast<CData>(rnd());
        check(!ua.neq(ub), "unpacked-eq", words, 0, 0);
        ub[rnd() % 5] ^= 1;
        check(ua.neq(ub), "unpacked-neq", words, 0, 0);
        VlUnpacked<VlUnpacked<QData, 3>, 2> na, nb;
        for (int k = 0; k < 2; ++k)
            for (int j = 0; j < 3; ++j) na[k][j] = nb[k][j] = rnd();
        check(!na.neq(nb), "nested-eq", words, 0, 0);
        nb[1][2] ^= 1ULL << 40;
        check(na.neq(nb), "nested-neq", words, 0, 0);
        VlUnpacked<double, 2> da, db;
        da[0] = db[0] = 0.0;
        da[1] = 0.0;
        db[1] = -0.0;
        check(!da.neq(db), "double-signed-zero", words, 0, 0);
    }
    for (IData lsb = 0; lsb < static_cast<IData>(obits); lsb += 1 + (lsb % 5)) {
        for (IData width = 1; lsb + width <= static_cast<IData>(obits); width += 1 + (width % 11)) {
            const int ow = VL_WORDS_I(width);
            std::vector<EData> s1(ow + 2, 0xdeadbeefU), s2(ow + 2, 0xdeadbeefU);
            VL_SEL_WWII(width, obits, s1.data(), l.data(), lsb, width);
            ref::sel(width, obits, s2.data(), l.data(), lsb, width);
            check(std::memcmp(s1.data(), s2.data(), (ow + 2) * 4) == 0, "sel", obits, lsb, width);
        }
    }
    // Inserts at every (lbit, hbit) pair on a stride, with and without an rbits clamp.
    for (int lbit = 0; lbit < obits; lbit += 1 + (lbit % 9)) {
        for (int hbit = lbit; hbit < obits + 3; hbit += 1 + (hbit % 13)) {
            const int src_words = VL_WORDS_I(hbit - lbit + 1) + 1;
            std::vector<EData> src(src_words);
            fill(src);
            std::vector<EData> d1(words + 4), d2(words + 4);
            fill(d1);
            d2 = d1;
            _vl_insert_WW(d1.data(), src.data(), hbit, lbit, obits);
            ref::insert_ww(d2.data(), src.data(), hbit, lbit, obits);
            check(std::memcmp(d1.data(), d2.data(), (words + 4) * 4) == 0, "insert", obits, lbit, hbit);
        }
    }
    // Concatenations through the public entry points.
    {
        const int rbits = 1 + static_cast<int>(rnd() % obits);
        const int lbits = obits - rbits;
        if (lbits > 0) {
            std::vector<EData> c1(words + 2, 0), c2(words + 2, 0);
            VL_CONCAT_WWW(obits, lbits, rbits, c1.data(), l.data(), r.data());
            for (int i = 0; i < VL_WORDS_I(rbits); ++i) c2[i] = r[i];
            for (int i = VL_WORDS_I(rbits); i < VL_WORDS_I(obits); ++i) c2[i] = 0;
            ref::insert_ww(c2.data(), l.data(), rbits + lbits - 1, rbits, 0);
            check(std::memcmp(c1.data(), c2.data(), words * 4) == 0, "concat", obits, lbits, rbits);
        }
    }
}

int main(int argc, char* argv[]) {
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get()}};
    for (int words = 1; words <= 70; ++words) {
        for (int rep = 0; rep < 3; ++rep) testWords(words);
    }
    if (g_fail) {
        printf("%%Error: %d mismatches\n", g_fail);
        return 10;
    }
#ifdef VL_SIMD_WORDS
    printf("simd words=%d\n", VL_SIMD_WORDS);
#else
    printf("simd words=scalar\n");
#endif
    printf("*-* All Finished *-*\n");
    topp->final();
    return 0;
}
