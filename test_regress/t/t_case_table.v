// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test V3Case constant-result case -> ConstPool lookup table lowering.
// Each qualifying case below must still compute identical results; the
// .pl checks the stats counter for the expected number of tables.  The
// expected-value functions deliberately use if/else chains so they are
// not themselves lowered to tables.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc;
   initial cyc = 0;

   // Result wires under test
   logic [7:0] a;  // blocking-assign arms + default   -> table
   logic [7:0] b;  // function return arms + default   -> table
   logic [7:0] c;  // comb mirror of the NBA case      -> table
   logic [7:0] d;  // full coverage, no default        -> table
   logic [7:0] e;  // multi-label items + default      -> table
   logic [7:0] f;  // only 3 arms: below minimum       -> tree
   logic [7:0] g;  // casex: never tabled              -> tree
   logic [7:0] h;  // arms assign different vars       -> tree
   logic [7:0] i;  // non-constant arm                 -> tree
   logic [7:0] q;  // registered version of the case   -> table via NBA

   // Independent references: if/else chains, never case statements.
   function automatic logic [7:0] expected(input logic [3:0] x);
      if (x == 4'd0) return 8'd10;
      else if (x == 4'd1) return 8'd11;
      else if (x == 4'd2) return 8'd12;
      else if (x == 4'd3) return 8'd13;
      else if (x == 4'd4) return 8'd14;
      else if (x == 4'd5) return 8'd15;
      else if (x == 4'd6) return 8'd16;
      else if (x == 4'd7) return 8'd17;
      else if (x == 4'd8) return 8'd18;
      else return 8'd99;
   endfunction

   function automatic logic [7:0] ftable(input logic [3:0] x);
      case (x)
        4'd0: return 8'd20;
        4'd1: return 8'd21;
        4'd2: return 8'd22;
        4'd3: return 8'd23;
        4'd4: return 8'd24;
        4'd5: return 8'd25;
        4'd6: return 8'd26;
        4'd7: return 8'd27;
        4'd8: return 8'd28;
        default: return 8'd88;
      endcase
   endfunction

   function automatic logic [7:0] expected_f(input logic [3:0] x);
      if (x == 4'd0) return 8'd20;
      else if (x == 4'd1) return 8'd21;
      else if (x == 4'd2) return 8'd22;
      else if (x == 4'd3) return 8'd23;
      else if (x == 4'd4) return 8'd24;
      else if (x == 4'd5) return 8'd25;
      else if (x == 4'd6) return 8'd26;
      else if (x == 4'd7) return 8'd27;
      else if (x == 4'd8) return 8'd28;
      else return 8'd88;
   endfunction

   // Full-coverage 3-bit decoder, no default arm.
   function automatic logic [7:0] expected_d(input logic [2:0] x);
      if (x == 3'd0) return 8'd30;
      else if (x == 3'd1) return 8'd31;
      else if (x == 3'd2) return 8'd32;
      else if (x == 3'd3) return 8'd33;
      else if (x == 3'd4) return 8'd34;
      else if (x == 3'd5) return 8'd35;
      else if (x == 3'd6) return 8'd36;
      else return 8'd37;
   endfunction

   // Multi-label items share statements.
   function automatic logic [7:0] expected_e(input logic [3:0] x);
      if (x == 4'd0 || x == 4'd1 || x == 4'd2) return 8'd40;
      else if (x == 4'd3 || x == 4'd4) return 8'd41;
      else if (x == 4'd5) return 8'd42;
      else if (x == 4'd6) return 8'd43;
      else if (x == 4'd7) return 8'd44;
      else if (x == 4'd8) return 8'd45;
      else if (x == 4'd9) return 8'd46;
      else if (x == 4'd10) return 8'd47;
      else return 8'd77;
   endfunction

   function automatic logic [7:0] expected_q(input logic [3:0] x);
      if (x == 4'd0) return 8'd90;
      else if (x == 4'd1) return 8'd91;
      else if (x == 4'd2) return 8'd92;
      else if (x == 4'd3) return 8'd93;
      else if (x == 4'd4) return 8'd94;
      else if (x == 4'd5) return 8'd95;
      else if (x == 4'd6) return 8'd96;
      else if (x == 4'd7) return 8'd97;
      else if (x == 4'd8) return 8'd98;
      else return 8'd99;
   endfunction

   logic [3:0] cyc4;
   logic [2:0] cyc3;
   logic [7:0] h2;

   always_comb begin
      cyc4 = cyc[3:0];
      cyc3 = cyc[2:0];

      // (a) blocking assign arms, default present -> table
      case (cyc4)
        4'd0: a = 8'd10;
        4'd1: a = 8'd11;
        4'd2: a = 8'd12;
        4'd3: a = 8'd13;
        4'd4: a = 8'd14;
        4'd5: a = 8'd15;
        4'd6: a = 8'd16;
        4'd7: a = 8'd17;
        4'd8: a = 8'd18;
        default: a = 8'd99;
      endcase

      // (b) function with return arms -> table inside function
      b = ftable(cyc4);

      // (c) same shape as the NBA case below, for comb checking
      case (cyc4)
        4'd0: c = 8'd90;
        4'd1: c = 8'd91;
        4'd2: c = 8'd92;
        4'd3: c = 8'd93;
        4'd4: c = 8'd94;
        4'd5: c = 8'd95;
        4'd6: c = 8'd96;
        4'd7: c = 8'd97;
        4'd8: c = 8'd98;
        default: c = 8'd99;
      endcase

      // (d) full coverage without default -> table
      case (cyc3)
        3'd0: d = 8'd30;
        3'd1: d = 8'd31;
        3'd2: d = 8'd32;
        3'd3: d = 8'd33;
        3'd4: d = 8'd34;
        3'd5: d = 8'd35;
        3'd6: d = 8'd36;
        3'd7: d = 8'd37;
      endcase

      // (e) multi-label items -> table
      case (cyc4)
        4'd0, 4'd1, 4'd2: e = 8'd40;
        4'd3, 4'd4:     e = 8'd41;
        4'd5:           e = 8'd42;
        4'd6:           e = 8'd43;
        4'd7:           e = 8'd44;
        4'd8:           e = 8'd45;
        4'd9:           e = 8'd46;
        4'd10:          e = 8'd47;
        default:        e = 8'd77;
      endcase

      // (f) too few arms -> stays a compare tree
      case (cyc4)
        4'd0: f = 8'd50;
        4'd1: f = 8'd51;
        4'd2: f = 8'd52;
        default: f = 8'd79;
      endcase

      // (g) casex -> never tabled
      /*verilator lint_off CASEX*/
      casex (cyc4)
        4'b000x: g = 8'd60;
        4'b001x: g = 8'd61;
        4'b01x0: g = 8'd62;
        4'b01x1: g = 8'd63;
        4'b1xxx: g = 8'd64;
        default: g = 8'd78;
      endcase
      /*verilator lint_on CASEX*/

      // (h) arms write different variables -> stays a tree
      h2 = 8'd0;
      case (cyc4)
        4'd0: begin h = 8'd70; h2 = 8'd1; end
        4'd1: h = 8'd71;
        4'd2: h = 8'd72;
        4'd3: h = 8'd73;
        4'd4: h = 8'd74;
        4'd5: h = 8'd75;
        4'd6: h = 8'd76;
        4'd7: h = 8'd77;
        4'd8: h = 8'd78;
        default: h = 8'd79;
      endcase

      // (i) non-constant arm -> stays a tree
      case (cyc4)
        4'd0: i = 8'd80;
        4'd1: i = 8'(cyc4) + 8'd1;
        4'd2: i = 8'd82;
        4'd3: i = 8'd83;
        4'd4: i = 8'd84;
        4'd5: i = 8'd85;
        4'd6: i = 8'd86;
        4'd7: i = 8'd87;
        4'd8: i = 8'd88;
        default: i = 8'd89;
      endcase
   end

   // (q) nonblocking arms -> table, registered output
   always_ff @(posedge clk) begin
      case (cyc4)
        4'd0: q <= 8'd90;
        4'd1: q <= 8'd91;
        4'd2: q <= 8'd92;
        4'd3: q <= 8'd93;
        4'd4: q <= 8'd94;
        4'd5: q <= 8'd95;
        4'd6: q <= 8'd96;
        4'd7: q <= 8'd97;
        4'd8: q <= 8'd98;
        default: q <= 8'd99;
      endcase
   end

   // Registered images so negedge checks see settled values.
   logic [7:0] a_r, b_r, c_r, d_r, e_r, f_r, g_r, h_r, i_r, q_r;
   logic [3:0] cyc_r;

   always_ff @(posedge clk) begin
      cyc_r <= cyc[3:0];
      a_r <= a;
      b_r <= b;
      c_r <= c;
      d_r <= d;
      e_r <= e;
      f_r <= f;
      g_r <= g;
      h_r <= h;
      i_r <= i;
      q_r <= q;
   end

   task automatic check(input string name, input logic [7:0] got,
                        input logic [7:0] exp);
      if (got !== exp) begin
         $display("FAIL %s: got %0d exp %0d (cyc_r %0d)", name, got, exp, cyc_r);
         $stop;
      end
   endtask

   always @(negedge clk) begin
      check("a", a_r, expected(cyc_r));
      check("b", b_r, expected_f(cyc_r));
      check("c", c_r, expected_q(cyc_r));
      check("d", d_r, expected_d(cyc_r[2:0]));
      check("e", e_r, expected_e(cyc_r));
      // q_r captured q one edge after q captured f(cyc4); cyc_r is the
      // producing cyc, so q corresponds to the *previous* cyc value.
      // At cyc_r == 0 q_r still holds its pre-first-edge value.
      if (cyc_r != 4'd0) check("q", q_r, expected_q(cyc_r - 4'd1));

      // f: 3-arm tree, values 50/51/52/79
      check("f", f_r,
            (cyc_r == 4'd0) ? 8'd50
            : (cyc_r == 4'd1) ? 8'd51
            : (cyc_r == 4'd2) ? 8'd52
                              : 8'd79);

      // g: casex -- 'x' in a label is a don't-care.  The patterns match:
      //   000x -> {0,1}  001x -> {2,3}  01x0 -> {4,6}  01x1 -> {5,7}
      //   1xxx -> {8..15}
      begin
         automatic logic [7:0] gexp;
         if (cyc_r == 4'd0 || cyc_r == 4'd1) gexp = 8'd60;
         else if (cyc_r == 4'd2 || cyc_r == 4'd3) gexp = 8'd61;
         else if (cyc_r == 4'd4 || cyc_r == 4'd6) gexp = 8'd62;
         else if (cyc_r == 4'd5 || cyc_r == 4'd7) gexp = 8'd63;
         else gexp = 8'd64;
         check("g", g_r, gexp);
      end

      // h: main variable takes arm values; h2 side effect only on arm 0
      check("h", h_r,
            (cyc_r == 4'd0) ? 8'd70
            : (cyc_r == 4'd1) ? 8'd71
            : (cyc_r == 4'd2) ? 8'd72
            : (cyc_r == 4'd3) ? 8'd73
            : (cyc_r == 4'd4) ? 8'd74
            : (cyc_r == 4'd5) ? 8'd75
            : (cyc_r == 4'd6) ? 8'd76
            : (cyc_r == 4'd7) ? 8'd77
            : (cyc_r == 4'd8) ? 8'd78
                              : 8'd79);

      // i: arm 1 is cyc4+1, rest constant
      check("i", i_r,
            (cyc_r == 4'd0) ? 8'd80
            : (cyc_r == 4'd1) ? 8'(cyc_r) + 8'd1
            : (cyc_r == 4'd2) ? 8'd82
            : (cyc_r == 4'd3) ? 8'd83
            : (cyc_r == 4'd4) ? 8'd84
            : (cyc_r == 4'd5) ? 8'd85
            : (cyc_r == 4'd6) ? 8'd86
            : (cyc_r == 4'd7) ? 8'd87
            : (cyc_r == 4'd8) ? 8'd88
                              : 8'd89);
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
