// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Etienne Cimon.
// SPDX-License-Identifier: CC0-1.0

// split_var on unpacked arrays whose declaration follows their uses in the
// module's statement list: written after the uses at module level, and
// declared inside a generate block (V3Begin hoists such a declaration to the
// end of the module, after every reference). Every reference must be split,
// or the ones seen before the declaration keep pointing at the deleted array.

module t (clk);
  input clk;
  integer cyc = 0;

  // Uses before the declaration (legal SystemVerilog).
  wire [1:0] out0 = ack_g[0];
  wire [1:0] out1 = ack_g[1];
  logic [1:0] ack_g [2] /*verilator split_var*/;
  for (genvar h = 0; h < 2; h++) begin : gen_h
    for (genvar p = 0; p < 2; p++) begin : gen_p
      assign ack_g[h][p] = cyc[p] & (cyc[2] == h[0]);
    end
  end

  // Declared inside a generate block, used inside it (the g6lc_smt_csr_bank shape).
  wire [1:0] bout0, bout1;
  if (1) begin : gen_banked
    logic [1:0] bank_g [2] /*verilator split_var*/;
    for (genvar h = 0; h < 2; h++) begin : gen_bh
      for (genvar p = 0; p < 2; p++) begin : gen_bp
        assign bank_g[h][p] = ~cyc[p] & (cyc[3] == h[0]);
      end
    end
    assign bout0 = bank_g[0];
    assign bout1 = bank_g[1];
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (out0 != (cyc[1:0] & {2{cyc[2] == 1'b0}})) $stop;
    if (out1 != (cyc[1:0] & {2{cyc[2] == 1'b1}})) $stop;
    if (bout0 != (~cyc[1:0] & {2{cyc[3] == 1'b0}})) $stop;
    if (bout1 != (~cyc[1:0] & {2{cyc[3] == 1'b1}})) $stop;
    if (cyc == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
