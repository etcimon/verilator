// DESCRIPTION: Verilator: Square masked transpose and near misses
// Copyright 2026 Etienne Cimon
// SPDX-License-Identifier: CC0-1.0
module probe #(parameter int MODE=0) (
    input logic [8:0][8:0] rows,
    input logic [8:0] mask, other,
    output logic [8:0] out,
    output logic watch_bit
);
   logic [8:0][8:0] cols;
   for (genvar c=0; c<9; ++c) begin
      for (genvar r=0; r<9; ++r)
        assign cols[c][r] = rows[r][(MODE == 1 && r == 3) ? 8-c : c];
      assign out[c] = |(cols[c] & ((MODE == 2 && c == 0) ? other : mask));
   end
   assign watch_bit = MODE == 3 ? cols[7][3] : 1'b0;
endmodule

module t(input clk);
   logic [80:0] rows = 81'h1659351d9e5b47f0139a1;
   logic [8:0] mask = '0;
   logic [8:0] out[4];
   logic [3:0] watch_bits;
   int unsigned cyc = 0;
   for (genvar m=0; m<4; ++m) begin
      probe #(m) p(rows, mask, ~mask, out[m], watch_bits[m]);
   end
   always @(posedge clk) begin
      for (int m=0; m<4; ++m) begin
         for (int c=0; c<9; ++c) begin
            logic b;
            b = 0;
            for (int r=0; r<9; ++r)
              b |= ((m == 2 && c == 0) ? !mask[r] : mask[r])
                   && rows[r*9 + ((m == 1 && r == 3) ? 8-c : c)];
            if (out[m][c] !== b) $stop;
         end
      end
      if (watch_bits !== {rows[34],3'b0}) $stop;
      rows <= {rows[31:0],rows[80:32]} + 81'h15721a6d782;
      mask <= mask + 9'd31;
      cyc <= cyc + 1;
      if (cyc == 511) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
