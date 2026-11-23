// DESCRIPTION: Verilator: Check DFG bitwise 2-way mux packing
// Copyright 2026 Etienne Cimon
// SPDX-License-Identifier: CC0-1.0
module t(input logic clk);
   logic [63:0] a = 64'h82df8104571a3529, b = 64'hd7cc4390fdd23311;
   logic [31:0] mux_or, mux_cond, mux_bad;
   int unsigned cyc = 0;
   wire sel = cyc[0];

   // Pattern 1: (sel & a[i]) | (~sel & b[i]) with shifted offsets
   for (genvar k = 0; k < 32; ++k) begin : gen_or
      assign mux_or[k] = (sel & a[k + 3]) | (~sel & b[k + 7]);
   end

   // Pattern 2: sel ? a[i] : b[i]
   for (genvar k = 0; k < 32; ++k) begin : gen_cond
      assign mux_cond[k] = (~sel) ? b[k + 1] : a[k + 5];
   end

   // Negative control: non-contiguous stride (must stay exact, not packed)
   for (genvar k = 0; k < 32; ++k) begin : gen_bad
      assign mux_bad[k] = (sel & a[k * 2]) | (~sel & b[k * 2 + 1]);
   end

   always @(posedge clk) begin
      logic [31:0] exp_or, exp_cond, exp_bad;
      exp_or = sel ? a[34:3] : b[38:7];
      exp_cond = (~sel) ? b[32:1] : a[36:5];
      for (int k = 0; k < 32; ++k) exp_bad[k] = sel ? a[k * 2] : b[k * 2 + 1];
      if (mux_or !== exp_or) $stop;
      if (mux_cond !== exp_cond) $stop;
      if (mux_bad !== exp_bad) $stop;
      a <= {a[16:0], a[63:17]} ^ b;
      b <= b + 64'h9e3779b97f4a7c15;
      cyc <= cyc + 1;
      if (cyc == 256) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
