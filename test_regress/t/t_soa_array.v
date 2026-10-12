// DESCRIPTION: Verilator: Packed element table + rolled NBA loop
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc;
   initial cyc = 0;

   // Packed array, touched only per element. V3Soa turns this into an
   // unpacked table and leaves the clocked scan rolled.
   logic [15:0][7:0] mem;
   logic [7:0] seen;

   initial begin
      for (int i = 0; i < 16; i++) mem[i] = 8'd0;
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      for (int i = 0; i < 16; i++) begin
         mem[i] <= mem[i] + 8'd1;
      end
      // Must observe the pre-commit value. The shadow copy-back is an NBA.
      seen <= mem[0];
   end

   always @(negedge clk) begin
      if (cyc == 5) begin
         if (mem[0] !== 8'd5) $stop;
         if (mem[7] !== 8'd5) $stop;
         if (mem[15] !== 8'd5) $stop;
         if (seen !== 8'd4) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
