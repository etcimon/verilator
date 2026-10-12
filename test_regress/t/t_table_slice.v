// DESCRIPTION: Verilator: Sliced lookup tables for a wide decoder
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// One 32-bit instruction feeds two independent fields. A single table would
// be 2^32 entries. Each output reads only its own field, so the block becomes
// two small tables.
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 1;
   logic [31:0] instr;
   logic [47:0] op_hit;
   logic [7:0] f3_hit;

   // Full-vector assigns. A bit-select on the left is not table-simulatable,
   // and the output must not be read (that would mix it into the input set).
   always_comb begin
      op_hit = '0;
      f3_hit = '0;
      for (int i = 0; i < 48; i++) begin
         if (instr[6:0] == i[6:0]) op_hit = 48'h1 << i;
      end
      for (int k = 0; k < 8; k++) begin
         if (instr[14:12] == k[2:0]) f3_hit = 8'h1 << k;
      end
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         // opcode 0010011 (19), funct3 000
         instr <= 32'b0000000_00000_00000_000_00000_0010011;
      end
      if (cyc == 2) begin
         if (op_hit[19] !== 1'b1 || op_hit[3] !== 1'b0) $stop;
         if (f3_hit[0] !== 1'b1 || f3_hit[2] !== 1'b0) $stop;
         // opcode 0000011 (3), funct3 010
         instr <= 32'b0000000_00000_00000_010_00000_0000011;
      end
      if (cyc == 3) begin
         if (op_hit[3] !== 1'b1 || op_hit[19] !== 1'b0) $stop;
         if (f3_hit[2] !== 1'b1 || f3_hit[0] !== 1'b0) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
