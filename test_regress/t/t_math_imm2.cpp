// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <vector>

#include "Vt_math_imm2.h"

double sc_time_stamp() { return 0; }

QData MaskVal(int lbit, int hbit) {
    QData val;
    for (val = 0; lbit <= hbit; lbit++) val |= (1ULL << lbit);
    return val;
}

static bool checkWideInsertBounds() {
    const WData rhs[] = {0xfedcba98U, 0x76543210U, 0xdeadbeefU, 0x13579bdfU};
    for (int rbits : {65, 95, 96, 127, 128, 191, 192, 193}) {
        const int words = VL_WORDS_I(rbits);
        for (int width : {1, 8, 31, 32, 37, 63, 64, 65, 97, 128}) {
            for (int lsb = 0; lsb <= rbits + 2; ++lsb) {
                std::vector<WData> data(words + 10, 0xa5a5a5a5U);
                data[words] &= VL_MASK_E(rbits);
                std::vector<WData> expected = data;
                for (int bit = 0; bit < width && lsb + bit < rbits; ++bit) {
                    const int target = lsb + bit;
                    const WData mask = 1U << (target & 31);
                    WData& word = expected[1 + target / 32];
                    word = (word & ~mask) | (((rhs[bit / 32] >> (bit & 31)) & 1U)
                                             << (target & 31));
                }
                if (width <= 32) {
                    VL_ASSIGNSEL_WI(rbits, width, lsb, data.data() + 1, rhs[0]);
                } else if (width <= 64) {
                    const QData value = (static_cast<QData>(rhs[1]) << 32) | rhs[0];
                    VL_ASSIGNSEL_WQ(rbits, width, lsb, data.data() + 1, value);
                } else {
                    VL_ASSIGNSEL_WW(rbits, width, lsb, data.data() + 1, rhs);
                }
                if (data != expected) {
                    printf("%%Error: wide insert bounds rbits=%d width=%d lsb=%d\n", rbits,
                           width, lsb);
                    return false;
                }
            }
        }
    }
    return true;
}

int main(int argc, char* argv[]) {
    Verilated::debug(0);
    Verilated::commandArgs(argc, argv);
    if (!checkWideInsertBounds()) return 1;

    VM_PREFIX* sim = new VM_PREFIX;
    int lbit, hbit;

    int errs = 0;
    for (lbit = 0; lbit < 32; lbit++) {
        for (hbit = lbit; hbit < 32; hbit++) {
            QData expected;

            sim->LowMaskSel_Bot = lbit;
            sim->LowMaskSel_Top = lbit;
            sim->HighMaskSel_Bot = hbit;
            sim->HighMaskSel_Top = hbit;

            sim->eval();

            expected = ((MaskVal(sim->LowMaskSel_Top, sim->HighMaskSel_Top) << 32ULL)
                        | MaskVal(sim->LowMaskSel_Bot, sim->HighMaskSel_Bot));

            if (sim->LogicImm != expected) {
                printf("%%Error: %d.%d,%d.%d -> %016" PRIx64 "/%016" PRIx64 " -> %016" PRIx64
                       " (expected %016" PRIx64 ")\n",
                       sim->LowMaskSel_Top, sim->HighMaskSel_Top, sim->LowMaskSel_Bot,
                       sim->HighMaskSel_Bot, sim->LowLogicImm, sim->HighLogicImm, sim->LogicImm,
                       expected);
                errs = 1;
            }
        }
    }

    sim->final();
    VL_DO_DANGLING(delete sim, sim);

    if (errs) {
        vl_stop(__FILE__, __LINE__, "TOP-cpp");
        exit(10);
    } else {
        printf("*-* All Finished *-*\n");
        return 0;
    }
}
