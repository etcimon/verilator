// DESCRIPTION: Verilator: tag wakeup nest -> waiter bitmask
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   localparam int DEPTH = 8;
   localparam int NR_WB = 4;
   localparam int TW = 3;

   typedef struct packed {
      logic          valid;
      logic          rs1_rdy;
      logic          rs2_rdy;
      logic          fpr_rs1;
      logic [TW-1:0] prs1;
      logic [TW-1:0] prs2;
   } entry_t;

   entry_t [DEPTH-1:0] q, q_wake;
   logic [DEPTH-1:0] kill;
   logic [NR_WB-1:0] wb_valid;
   logic [NR_WB-1:0][TW-1:0] wb_prd;

   integer cyc;
   initial cyc = 0;

   // Same shape as an issue-queue wakeup: a per-entry prefix, then a
   // writeback scan that sets ready bits when a source tag matches.
   always_comb begin
      q_wake = q;
      for (int unsigned e = 0; e < DEPTH; e++) begin
         if (q[e].valid && kill[e]) q_wake[e].valid = 1'b0;
         if (q_wake[e].valid) begin
            for (int unsigned w = 0; w < NR_WB; w++) begin
               if (wb_valid[w] && wb_prd[w] != '0) begin
                  if (!q_wake[e].fpr_rs1 && q_wake[e].prs1 == wb_prd[w])
                    q_wake[e].rs1_rdy = 1'b1;
                  if (q_wake[e].prs2 == wb_prd[w])
                    q_wake[e].rs2_rdy = 1'b1;
               end
            end
         end
      end
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         // {valid, rs1_rdy, rs2_rdy, fpr_rs1, prs1, prs2}
         q[0] <= {1'b1, 1'b0, 1'b0, 1'b0, 3'd1, 3'd3};
         q[1] <= {1'b1, 1'b0, 1'b0, 1'b0, 3'd1, 3'd0};
         q[2] <= {1'b1, 1'b0, 1'b0, 1'b1, 3'd3, 3'd1};
         q[3] <= {1'b0, 1'b0, 1'b0, 1'b0, 3'd1, 3'd1};
         q[4] <= {1'b1, 1'b0, 1'b0, 1'b0, 3'd0, 3'd0};
         q[5] <= {1'b1, 1'b0, 1'b0, 1'b0, 3'd4, 3'd4};
         q[6] <= {1'b1, 1'b1, 1'b0, 1'b0, 3'd5, 3'd2};
         q[7] <= {1'b1, 1'b0, 1'b0, 1'b0, 3'd5, 3'd5};
         kill <= 8'b0010_0000;
         wb_valid <= 4'b1111;
         wb_prd[0] <= 3'd1;
         wb_prd[1] <= 3'd5;
         wb_prd[2] <= 3'd0;
         wb_prd[3] <= 3'd4;
      end
      if (cyc == 1) begin
         if (q_wake[0].valid !== 1'b1 || q_wake[0].rs1_rdy !== 1'b1 || q_wake[0].rs2_rdy !== 1'b0)
           $stop;
         if (q_wake[0].prs1 !== 3'd1 || q_wake[0].prs2 !== 3'd3) $stop;
         if (q_wake[1].rs1_rdy !== 1'b1 || q_wake[1].rs2_rdy !== 1'b0) $stop;
         // FP source does not wake on the integer tag. rs2 still does.
         if (q_wake[2].rs1_rdy !== 1'b0 || q_wake[2].rs2_rdy !== 1'b1) $stop;
         if (q_wake[3].valid !== 1'b0 || q_wake[3].rs1_rdy !== 1'b0) $stop;
         // Tag 0 is a real value but writeback 0 is ignored.
         if (q_wake[4].rs1_rdy !== 1'b0 || q_wake[4].rs2_rdy !== 1'b0) $stop;
         // Killed before the tag-4 writeback is applied.
         if (q_wake[5].valid !== 1'b0 || q_wake[5].rs1_rdy !== 1'b0 || q_wake[5].rs2_rdy !== 1'b0)
           $stop;
         if (q_wake[6].rs1_rdy !== 1'b1 || q_wake[6].rs2_rdy !== 1'b0) $stop;
         if (q_wake[7].rs1_rdy !== 1'b1 || q_wake[7].rs2_rdy !== 1'b1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
