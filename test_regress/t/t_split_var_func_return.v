// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Etienne Cimon.
// SPDX-License-Identifier: CC0-1.0

// Auto field-split (-ffield-split) must not mark a function's return
// variable: it is AstFunc::fvarp, an operand slot that cannot carry a
// nextp list. The hyp8 LSQ lane_be_table hit this as
// "AstFunc::fvarp() cannot have a non nullptr nextp()".

module t (clk);
  input clk;
  integer cyc = 0;

  localparam int LANES = 8;

  // Byte-enable table built through constant selects on the function
  // return variable, in nested loops (the g6lc_lsq lane_be_table shape).
  function automatic logic [31:0][LANES-1:0] tbl();
    logic [LANES-1:0] m;
    for (int unsigned s = 0; s < 4; s++) begin
      for (int unsigned off = 0; off < 8; off++) begin
        m = '0;
        for (int unsigned b = 0; b < LANES; b++)
          if (b < (1 << s)) m[b] = 1'b1;
        tbl[{s[1:0], off[2:0]}] = m << off[2:0];
      end
    end
  endfunction

  localparam logic [31:0][LANES-1:0] TAB = tbl();

  function automatic logic [LANES-1:0] rd(input logic [4:0] i);
    return TAB[i];
  endfunction

  // A non-constant call keeps tbl() live past parameter folding so the
  // return variable reaches V3SplitVar as a real function.
  logic [31:0][LANES-1:0] x;
  always_comb x = tbl();

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) begin
      // localparam table, read at runtime indices
      if (rd(5'd0)  !== 8'h01) $stop;
      if (rd(5'd9)  !== 8'h06) $stop;
      if (rd(5'd17) !== 8'h1e) $stop;
      if (rd(5'd25) !== 8'hfe) $stop;
      if (rd(5'd31) !== 8'h80) $stop;
      // live-call result agrees
      if (x[0]   !== 8'h01) $stop;
      if (x[9]   !== 8'h06) $stop;
      if (x[17]  !== 8'h1e) $stop;
      if (x[25]  !== 8'hfe) $stop;
      if (x[31]  !== 8'h80) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
