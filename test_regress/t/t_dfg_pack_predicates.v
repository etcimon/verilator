// DESCRIPTION: Verilator: Check the predicate packer against a vector expression
// Copyright 2026 Etienne Cimon
// SPDX-License-Identifier: CC0-1.0
module t(input clk);
   logic [63:0] a = 64'h82df8104571a3529, b = 64'hd7cc4390fdd23311;
   logic [55:0] ready;
   int unsigned cyc = 0;
   for (genvar k = 0; k < 56; ++k)
     assign ready[k] = a[k+2] && !(b[k+5] && !cyc[0]);
   always @(posedge clk) begin
      if (ready !== (cyc[0] ? a[57:2] : a[57:2] & ~b[60:5])) $stop;
      a <= {a[16:0], a[63:17]} ^ b;
      b <= b + 64'h9e3779b97f4a7c15;
      cyc <= cyc + 1;
      if (cyc == 128) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
