// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Minimal model: the C++ main exercises the wide-word runtime kernels directly.
module t (/*AUTOARG*/
   // Outputs
   y,
   // Inputs
   a
   );
   input  [511:0] a;
   output [511:0] y;
   assign y = {a[255:0], a[511:256]} ^ (a << 37);
endmodule
