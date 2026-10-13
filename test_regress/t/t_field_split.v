// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Etienne Cimon.
// SPDX-License-Identifier: CC0-1.0

// A wide packed word that is only touched through constant byte selects,
// plus a constant whole-word reset, becomes one variable per byte.
// The whole-vector `wide` stays packed.
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [127:0] lanes;
   logic [127:0] wide;
   int cyc;

   initial begin
      lanes = '0;
      wide = '0;
      cyc = 0;
   end

   always_ff @(posedge clk) begin
      lanes[7:0] <= lanes[7:0] + 8'd1;
      lanes[15:8] <= lanes[15:8] + 8'd2;
      lanes[23:16] <= lanes[23:16] + 8'd3;
      lanes[31:24] <= lanes[31:24] + 8'd4;
      wide <= wide + 128'd1;
      cyc <= cyc + 1;
      if (cyc == 8) begin
         if (lanes[7:0] !== 8'd8) $stop;
         if (lanes[15:8] !== 8'd16) $stop;
         if (lanes[23:16] !== 8'd24) $stop;
         if (lanes[31:24] !== 8'd32) $stop;
         if (lanes[127:32] !== '0) $stop;
         if (wide !== 128'd8) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
