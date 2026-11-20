// DESCRIPTION: Verilator: mask-to-tag or-accumulate loop -> onehot guard + ctz
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

   // mask_to_tag shape: for (i) if (m[i]) out = out | W'(i);
   // The loop ORs the index of every set mask bit. For a one-hot or empty
   // mask that is exactly ctz(m), so V3Prio guards the loop with a
   // one-hot test and keeps the loop as the multi-bit fallback.

   // 16-bit mask -> VL_ONEHOT0_I / VL_CTZ_I
   logic [15:0] m16;
   logic [4:0] t16;
   function automatic logic [4:0] m2t16(input logic [15:0] m);
      m2t16 = '0;
      for (int unsigned i = 0; i < 16; i++)
        if (m[i]) m2t16 = m2t16 | 5'(i);
   endfunction
   assign t16 = m2t16(m16);

   // 48-bit mask -> VL_ONEHOT0_Q / VL_CTZ_Q
   logic [47:0] m48;
   logic [5:0] t48;
   function automatic logic [5:0] m2t48(input logic [47:0] m);
      m2t48 = '0;
      for (int unsigned i = 0; i < 48; i++)
        if (m[i]) m2t48 = m2t48 | 6'(i);
   endfunction
   assign t48 = m2t48(m48);

   // 72-bit mask -> VL_ONEHOT0_W / VL_CTZ_W (past the 64-bit helpers)
   logic [71:0] m72;
   logic [6:0] t72;
   function automatic logic [6:0] m2t72(input logic [71:0] m);
      m2t72 = '0;
      for (int unsigned i = 0; i < 72; i++)
        if (m[i]) m2t72 = m2t72 | 7'(i);
   endfunction
   assign t72 = m2t72(m72);

   // Same shape directly in always_comb -> VL_ONEHOT0_I / VL_CTZ_I
   logic [31:0] m32;
   logic [5:0] t32;
   always_comb begin
      t32 = 6'd0;
      for (int unsigned i = 0; i < 32; i++)
        if (m32[i]) t32 = t32 | 6'(i);
   end

   // Reject paths: these must stay plain loops (still functionally checked).
   // Descending bit order is a clz-style scan, not ctz.
   logic [5:0] tdesc;
   always_comb begin
      tdesc = 6'd0;
      for (int unsigned i = 0; i < 32; i++)
        if (m32[31-i]) tdesc = tdesc | 6'(i);
   end
   // OR-ing anything but the bare index is not an index accumulation.
   logic [5:0] tbad;
   always_comb begin
      tbad = 6'd0;
      for (int unsigned i = 0; i < 32; i++)
        if (m32[i]) tbad = tbad | 6'(i + 1);
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         m16 <= 16'h0000;
         m48 <= 48'h0000_0000_0000;
         m72 <= 72'h0000_0000_0000_0000_0000;
         m32 <= 32'h0000_0000;
      end
      if (cyc == 1) begin
         // All masks empty: every tag is the '0 initializer.
         if (t16 !== 5'd0 || t48 !== 6'd0 || t72 !== 7'd0 || t32 !== 6'd0) $stop;
         if (tdesc !== 6'd0 || tbad !== 6'd0) $stop;
         // Single set bits at the top of each mask.
         m16 <= 16'h8000;  // bit 15 -> 15
         m48 <= 48'd1 << 47;  // bit 47 -> 47
         m72 <= 72'd1 << 70;  // bit 70 -> 70
         m32 <= 32'h8000_0000;  // bit 31 -> 31
      end
      if (cyc == 2) begin
         if (t16 !== 5'd15 || t48 !== 6'd47 || t72 !== 7'd70 || t32 !== 6'd31) $stop;
         // tdesc: bit31 -> i=0 -> 0; tbad: i=31 -> 6'(32) = 32.
         if (tdesc !== 6'd0 || tbad !== 6'd32) $stop;
         // Multi-bit masks: the fallback loop ORs every set index.
         m16 <= 16'h0021;  // bits 0,5 -> 0|5 = 5
         m48 <= (48'd1 << 10) | (48'd1 << 20);  // 10|20 = 30
         m72 <= (72'd1 << 3) | (72'd1 << 70);  // 3|70 = 71
         m32 <= (32'd1 << 7) | (32'd1 << 8);  // 7|8 = 15
      end
      if (cyc == 3) begin
         if (t16 !== 5'd5 || t48 !== 6'd30 || t72 !== 7'd71 || t32 !== 6'd15) $stop;
         // bit 0 encodes as index 0, same as the empty mask.
         m16 <= 16'h0001;
         m48 <= 48'd1;
         m72 <= 72'd1;
         m32 <= 32'h0000_0003;  // bits 0,1
      end
      if (cyc == 4) begin
         if (t16 !== 5'd0 || t48 !== 6'd0 || t72 !== 7'd0) $stop;
         // t32: 0|1 = 1; tdesc: bits 0,1 -> i = 31,30 -> 31|30 = 31;
         // tbad: i+1 = 1,2 -> 1|2 = 3.
         if (t32 !== 6'd1 || tdesc !== 6'd31 || tbad !== 6'd3) $stop;
         m16 <= 16'h0408;  // bits 3,10 -> 3|10 = 11
         m48 <= 48'd1 << 20;  // single mid bit -> 20
         m72 <= (72'd1 << 40) | (72'd1 << 6);  // 40|6 = 46
         m32 <= 32'h0001_0000;  // bit 16 -> 16; tdesc i=15, tbad i+1=17
      end
      if (cyc == 5) begin
         if (t16 !== 5'd11 || t48 !== 6'd20 || t72 !== 7'd46 || t32 !== 6'd16) $stop;
         if (tdesc !== 6'd15 || tbad !== 6'd17) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
