// DESCRIPTION: Verilator: Dirty-bit change detect on a wide hybrid cut
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// `n` is written at a variable index, so it cannot be split. `keep` is a
// primary input held at 0 by the testbench: `n & {128{keep}}` is a real
// read, and the gate pass cannot delete it. The cycle is stable
// (p == zero-extend(seq), n == p with bit idx replaced) and wide enough
// that the hybrid trigger would otherwise compare the whole vector.
module t (/*AUTOARG*/
   // Inputs
   clk, keep
   );
   input clk;
   input keep;

   integer cyc = 1;
   logic [7:0] seq = 0;
   logic [6:0] idx = 0;
   logic bit_in = 0;
   logic [127:0] n;
   logic [127:0] p;

   always_comb begin
      n = p;
      n[idx] = bit_in;
   end
   always_comb p = {120'b0, seq} | (n & {128{keep}});

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         seq <= 8'h44;
         idx <= 7'd3;
         bit_in <= 1'b1;
      end
      if (cyc == 2) begin
         // bit 3 of 0x44 was 0; setting it yields 0x4c
         if (p !== 128'h44 || n !== 128'h4c) $stop;
         seq <= 8'h80;
         idx <= 7'd7;
         bit_in <= 1'b0;
      end
      if (cyc == 3) begin
         // bit 7 of 0x80 cleared
         if (p !== 128'h80 || n !== 128'h00) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
