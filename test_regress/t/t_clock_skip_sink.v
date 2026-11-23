// DESCRIPTION: Verilator: Test sink-domain clock-gated NBA comb deferral (ST and MT)
// Copyright 2026 Etienne Cimon
// SPDX-License-Identifier: CC0-1.0

module icg_cell (
    input  logic clk_i,
    input  logic en_i,
    output logic clk_o
);
    logic clk_en;
    /* verilator lint_off LATCH */
    /* verilator lint_off COMBDLY */
    always_latch begin
        if (clk_i == 1'b0) clk_en <= en_i;
    end
    /* verilator lint_on COMBDLY */
    /* verilator lint_on LATCH */
    assign clk_o = clk_i & clk_en;
endmodule

module gated_core (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic [63:0] global_bus_i,
    input  logic [31:0] seed_i,
    output logic [63:0] state_o
);
    /* verilator no_inline_module */
    logic [63:0] s0_q, s1_q;
    logic [63:0] s0_d, s1_d, mix_a, mix_b;

    // Multi-stage pure next-state comb tainted by global_bus_i (always-on clock),
    // but consumed ONLY by always_ff @(posedge clk_i or negedge rst_ni).
    always_comb begin
        mix_a = (s0_q ^ global_bus_i) + {32'd0, seed_i};
        mix_b = {mix_a[50:0], mix_a[63:51]} ^ (s1_q * 64'h9e3779b97f4a7c15);
        s0_d  = mix_b ^ (global_bus_i >> 3);
        s1_d  = (s0_q + mix_a) ^ {mix_b[31:0], mix_b[63:32]};
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            s0_q <= {32'h12345678, seed_i};
            s1_q <= {seed_i, 32'h87654321};
        end else begin
            s0_q <= s0_d;
            s1_q <= s1_d;
        end
    end

    assign state_o = s0_q ^ s1_q;
endmodule

module t (
    input logic clk
);
    int unsigned cyc = 0;
    logic rst_n = 1'b0;
    logic [63:0] global_bus_q = 64'h1122334455667788;
    logic en0, en1, gclk0, gclk1;
    logic [63:0] out0, out1;

    // Reference state (computed on ungated clk with explicit enable)
    logic [63:0] ref0_s0 = {32'h12345678, 32'h000000a5};
    logic [63:0] ref0_s1 = {32'h000000a5, 32'h87654321};
    logic [63:0] ref1_s0 = {32'h12345678, 32'h0000005a};
    logic [63:0] ref1_s1 = {32'h0000005a, 32'h87654321};

    // Core 0 sleeps periodically (50 on / 150 off); core 1 sleeps 200 cycles then wakes
    assign en0 = !rst_n || ((cyc % 200) < 50);
    assign en1 = !rst_n || ((cyc >= 210) && ((cyc % 250) < 40));

    icg_cell u_icg0 (.clk_i(clk), .en_i(en0), .clk_o(gclk0));
    icg_cell u_icg1 (.clk_i(clk), .en_i(en1), .clk_o(gclk1));

    gated_core u_core0 (
        .clk_i(gclk0), .rst_ni(rst_n),
        .global_bus_i(global_bus_q), .seed_i(32'h000000a5), .state_o(out0)
    );
    gated_core u_core1 (
        .clk_i(gclk1), .rst_ni(rst_n),
        .global_bus_i(global_bus_q), .seed_i(32'h0000005a), .state_o(out1)
    );

    logic en0_lat, en1_lat;
    always_ff @(negedge clk) begin
        en0_lat <= en0;
        en1_lat <= en1;
    end

    always_ff @(posedge clk) begin
        cyc <= cyc + 1;
        // Release reset at cyc 5, pulse async reset while core 1 sleeps at cyc 700
        if (cyc < 5 || (cyc >= 700 && cyc < 704)) begin
            rst_n <= 1'b0;
        end else begin
            rst_n <= 1'b1;
        end
        // Always-on global bus mutates every single cycle even while cores sleep
        global_bus_q <= (global_bus_q * 64'h5851f42d4c957f2d) + 64'h14057b7ef767814f;

        if (!rst_n) begin
            ref0_s0 <= {32'h12345678, 32'h000000a5};
            ref0_s1 <= {32'h000000a5, 32'h87654321};
            ref1_s0 <= {32'h12345678, 32'h0000005a};
            ref1_s1 <= {32'h0000005a, 32'h87654321};
        end else begin
            if (out0 !== (ref0_s0 ^ ref0_s1)) begin
                $display("FAIL core0 cyc=%0d got=%h exp=%h", cyc, out0, ref0_s0 ^ ref0_s1);
                $stop;
            end
            if (out1 !== (ref1_s0 ^ ref1_s1)) begin
                $display("FAIL core1 cyc=%0d got=%h exp=%h", cyc, out1, ref1_s0 ^ ref1_s1);
                $stop;
            end
            if (en0_lat) begin
                automatic logic [63:0] ma = (ref0_s0 ^ global_bus_q) + 64'h000000a5;
                automatic logic [63:0] mb = {ma[50:0], ma[63:51]} ^ (ref0_s1 * 64'h9e3779b97f4a7c15);
                ref0_s0 <= mb ^ (global_bus_q >> 3);
                ref0_s1 <= (ref0_s0 + ma) ^ {mb[31:0], mb[63:32]};
            end
            if (en1_lat) begin
                automatic logic [63:0] ma = (ref1_s0 ^ global_bus_q) + 64'h0000005a;
                automatic logic [63:0] mb = {ma[50:0], ma[63:51]} ^ (ref1_s1 * 64'h9e3779b97f4a7c15);
                ref1_s0 <= mb ^ (global_bus_q >> 3);
                ref1_s1 <= (ref1_s0 + ma) ^ {mb[31:0], mb[63:32]};
            end
        end

        if (cyc == 1500) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
