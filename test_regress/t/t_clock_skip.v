// DESCRIPTION: Verilator: skip stable per-instance combinational logic
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Two cores, clocks gated by en. Combo is q + side + 1, so a data change
// while the clock is stopped must not move y, but a side change must.
module core (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] side,
    output logic [7:0] y
);
    logic [7:0] q;
    always_ff @(posedge clk) q <= d;
    always_comb y = q + side + 8'd1;
endmodule

module t (/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    integer cyc;
    logic en0, en1;
    logic [7:0] d0, d1, side;
    logic [7:0] y0, y1;
    logic [7:0] y0_held, y1_held;
    logic c0, c1;

    assign c0 = clk & en0;
    assign c1 = clk & en1;
    core u0 (
        .clk(c0),
        .d(d0),
        .side(side),
        .y(y0)
    );
    core u1 (
        .clk(c1),
        .d(d1),
        .side(side),
        .y(y1)
    );

    initial begin
        cyc = 0;
        en0 = 1'b0;
        en1 = 1'b0;
        d0 = 8'h00;
        d1 = 8'h00;
        side = 8'h00;
    end

    always @(posedge clk) begin
        cyc <= cyc + 1;
        // Core 1 runs. Core 0 stays gated.
        if (cyc == 2) begin
            en0 <= 1'b0;
            en1 <= 1'b1;
            d0 <= 8'h10;
            d1 <= 8'h20;
            side <= 8'h00;
        end
        // d0 changes while core 0 is gated. y0 must hold.
        if (cyc == 6) begin
            y0_held <= y0;
            y1_held <= y1;
            d0 <= 8'ha5;
        end
        if (cyc == 8) begin
            if (y0 !== y0_held) begin
                $display("%%Error: gated d0 changed y0 %h -> %h", y0_held, y0);
                $stop;
            end
            // side is a combo input of both cores, so both outputs move.
            side <= 8'h03;
        end
        if (cyc == 9) begin
            if (y0 !== (y0_held + 8'h03)) begin
                $display("%%Error: side did not flow to gated y0 %h %h", y0_held, y0);
                $stop;
            end
            if (y1 !== (y1_held + 8'h03)) begin
                $display("%%Error: side did not flow to running y1 %h %h", y1_held, y1);
                $stop;
            end
            // Arm core 0. It captures on a later posedge of c0.
            en0 <= 1'b1;
            d0 <= 8'h11;
        end
        if (cyc == 12) begin
            if (y0 !== (8'h11 + side + 8'd1)) begin
                $display("%%Error: core0 missed enable y0=%h side=%h", y0, side);
                $stop;
            end
            if (y1 !== (8'h20 + side + 8'd1)) begin
                $display("%%Error: core1 lost state y1=%h side=%h", y1, side);
                $stop;
            end
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
