// DESCRIPTION: Verilator: Automatic split_var of a combinational cycle
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Bit-level this is acyclic. As two whole variables it is a combinational
// cycle, which is the false UNOPTFLAT split_var removes. No metacomment:
// the split plan has to mark both variables in this run.
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 1;
   logic [7:0] src;
   logic [7:0] a;
   logic [7:0] b;

   always_comb begin
      a[3:0] = b[3:0] ^ 4'h1;
      a[7:4] = b[7:4];
   end
   always_comb begin
      b[3:0] = a[7:4];
      b[7:4] = src[3:0];
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) src <= 8'h5;
      if (cyc == 2) begin
         // b[7:4] = 5, a[7:4] = 5, b[3:0] = 5, a[3:0] = 4
         if (a !== 8'h54 || b !== 8'h55) $stop;
         src <= 8'ha;
      end
      if (cyc == 3) begin
         // b[7:4] = a, a[7:4] = a, b[3:0] = a, a[3:0] = b
         if (a !== 8'hab || b !== 8'haa) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
