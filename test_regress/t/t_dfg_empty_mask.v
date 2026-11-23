// DESCRIPTION: Verilator: Do not skip a group containing a different lane mask
// Copyright 2026 Etienne Cimon
// SPDX-License-Identifier: CC0-1.0
module t(input clk);
   logic [7:0] cyc = 0;
   logic [7:0] m, other, result, mixed;
   logic [7:0][7:0] words = 64'h932d81f53e078c41;
   assign m = cyc[0] ? (cyc ^ 8'h15) : '0;
   assign other = ~m;
   for (genvar i=0; i<8; ++i) begin
      assign result[i] = m[i] & ~|(m & words[i]);
      assign mixed[i] = other[i] & |(m & words[7-i]);
   end
   always @(posedge clk) begin
      for (int i=0; i<8; ++i) begin
         if (result[i] !== (m[i] && (words[i] & m) == 0)) $stop;
         if (mixed[i] !== (other[i] && (words[7-i] & m) != 0)) $stop;
      end
      cyc <= cyc + 1;
      words <= {words[3:0],words[7:4]} + 64'h339b162fb46d3821;
      if (cyc == 127) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
