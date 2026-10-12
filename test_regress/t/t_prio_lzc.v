// DESCRIPTION: Verilator: lzc tree, find-first loop, and LSB grant -> ctz
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

   // WIDTH=4 lzc tree. The copy loop keeps the leaves on in_tmp, as lzc does
   // after MODE is folded, so the tree is not a straight view of in_i.
   logic [3:0] in_i;
   logic [1:0] cnt4;
   logic empty4;
   logic [3:0] in_tmp;
   logic [3:0][1:0] index_lut;
   logic [3:0] sel_nodes;
   logic [3:0][1:0] index_nodes;

   always_comb begin
      for (int unsigned i = 0; i < 4; i++) in_tmp[i] = in_i[i];
   end
   for (genvar j = 0; j < 4; j++) begin
      assign index_lut[j] = 2'(j);
   end
   assign sel_nodes[1] = in_tmp[0] | in_tmp[1];
   assign index_nodes[1] = (in_tmp[0] == 1'b1) ? index_lut[0] : index_lut[1];
   assign sel_nodes[2] = in_tmp[2] | in_tmp[3];
   assign index_nodes[2] = (in_tmp[2] == 1'b1) ? index_lut[2] : index_lut[3];
   assign sel_nodes[0] = sel_nodes[1] | sel_nodes[2];
   assign index_nodes[0] = (sel_nodes[1] == 1'b1) ? index_nodes[1] : index_nodes[2];
   assign cnt4 = index_nodes[0];
   assign empty4 = ~sel_nodes[0];

   // Odd width: the high leaf is a single bit, not a pair.
   logic [2:0] in3;
   logic [1:0] cnt3;
   logic empty3;
   logic [2:0][1:0] lut3;
   logic [3:0] sel3;
   logic [3:0][1:0] idx3;
   for (genvar j = 0; j < 3; j++) begin
      assign lut3[j] = 2'(j);
   end
   assign sel3[1] = in3[0] | in3[1];
   assign idx3[1] = (in3[0] == 1'b1) ? lut3[0] : lut3[1];
   assign sel3[2] = in3[2];
   assign idx3[2] = lut3[2];
   assign sel3[0] = sel3[1] | sel3[2];
   assign idx3[0] = (sel3[1] == 1'b1) ? idx3[1] : idx3[2];
   assign cnt3 = idx3[0];
   assign empty3 = ~sel3[0];

   logic [3:0] bits;
   logic [1:0] tern;
   logic [1:0] chain;
   assign tern = (bits[0] | bits[1]) ? (bits[0] ? 2'd0 : 2'd1) : (bits[2] ? 2'd2 : 2'd3);
   assign chain = bits[0] ? 2'd0 : bits[1] ? 2'd1 : bits[2] ? 2'd2 : 2'd3;

   logic [7:0] req;
   logic [2:0] idx;
   always_comb begin
      idx = 3'd7;
      for (int i = 0; i < 8; i++) begin
         if (req[i]) begin
            idx = i[2:0];
            break;
         end
      end
   end

   logic [7:0] reqm;
   logic [2:0] lidx;
   always_comb begin
      lidx = 3'd7;
      for (int i = 0; i < 8; i++) begin
         if (reqm[7-i]) begin
            lidx = i[2:0];
            break;
         end
      end
   end

   logic [7:0] gnt;
   logic [7:0] req2;
   logic found;
   always_comb begin
      found = 1'b0;
      for (int k = 0; k < 8; k++) begin
         gnt[k] = req2[k] && !found;
         found = found | req2[k];
      end
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         in_i <= 4'b0000;
         in3 <= 3'b000;
         bits <= 4'b0000;
         req <= 8'h00;
         reqm <= 8'h00;
         req2 <= 8'h00;
      end
      if (cyc == 1) begin
         if (cnt4 !== 2'd3 || empty4 !== 1'b1) $stop;
         if (cnt3 !== 2'd2 || empty3 !== 1'b1) $stop;
         if (tern !== 2'd3 || chain !== 2'd3) $stop;
         if (idx !== 3'd7 || lidx !== 3'd7) $stop;
         if (gnt !== 8'h00 || found !== 1'b0) $stop;
         in_i <= 4'b0001;
         in3 <= 3'b001;
         bits <= 4'b0001;
         req <= 8'h01;
         reqm <= 8'h80;
         req2 <= 8'h01;
      end
      if (cyc == 2) begin
         if (cnt4 !== 2'd0 || empty4 !== 1'b0) $stop;
         if (cnt3 !== 2'd0 || empty3 !== 1'b0) $stop;
         if (tern !== 2'd0 || chain !== 2'd0) $stop;
         if (idx !== 3'd0 || lidx !== 3'd0) $stop;
         if (gnt !== 8'h01 || found !== 1'b1) $stop;
         in_i <= 4'b0010;
         in3 <= 3'b010;
         bits <= 4'b0010;
         req <= 8'h10;
         reqm <= 8'h10;
         req2 <= 8'h12;
      end
      if (cyc == 3) begin
         if (cnt4 !== 2'd1 || empty4 !== 1'b0) $stop;
         if (cnt3 !== 2'd1 || empty3 !== 1'b0) $stop;
         if (tern !== 2'd1 || chain !== 2'd1) $stop;
         if (idx !== 3'd4 || lidx !== 3'd3) $stop;
         if (gnt !== 8'h02 || found !== 1'b1) $stop;
         in_i <= 4'b1000;
         in3 <= 3'b100;
         bits <= 4'b0100;
         req <= 8'h80;
         reqm <= 8'h01;
         req2 <= 8'h80;
      end
      if (cyc == 4) begin
         if (cnt4 !== 2'd3 || empty4 !== 1'b0) $stop;
         if (cnt3 !== 2'd2 || empty3 !== 1'b0) $stop;
         if (tern !== 2'd2 || chain !== 2'd2) $stop;
         if (idx !== 3'd7 || lidx !== 3'd7) $stop;
         if (gnt !== 8'h80 || found !== 1'b1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
