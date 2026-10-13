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

module cache_leaf (
    input logic clk,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] y
);
    logic [31:0] salt;
    always @(posedge clk) salt <= b;
    always_comb y = ((a * 32'd17) ^ ((b ^ salt) * 32'd29)) + 32'd7;
endmodule

// Kept out of line so the top-level probes below stay hierarchical references
// after scoping (the real-core probe shape), while the other instances inline.
module cache_parent (
    input logic clk,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] y
);
    /* verilator no_inline_module */
    logic [31:0] first, second;
    always_comb first = a + 32'd13;
    cache_leaf child (.clk(clk), .a(first), .b(b), .y(second));
    always_comb y = second ^ (a * 32'd31);
endmodule

module cache_partial (
    input logic clk,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] y
);
    logic [127:0] state = '0;
    always @(posedge clk or negedge clk) begin
        if (clk) state[a[3:0] * 8 +: 8] <= a[15:8];
        else state[95:64] <= b;
    end
    always_comb y = state[31:0] ^ state[63:32] ^ state[95:64] ^ state[127:96] ^ b;
endmodule

module cache_slice_reader #(parameter integer OFFSET = 0) (
    input logic clk,
    input logic [191:0] state,
    input logic [7:0] d,
    output logic [63:0] y
);
    logic [7:0] salt = 0;
    always @(posedge clk) if (d == 8'hff) salt <= d;
    always_comb y = 64'(state[OFFSET +: 37]) ^ {56'd0, salt};
endmodule

module cache_slices (
    input logic clk, gated_clk,
    input logic [31:0] d,
    output logic [63:0] y0, y1, y2, y3
);
    logic [191:0] state = '0;
    always @(posedge clk) begin
        if (d[7]) state <= {6{d}};
        else case (d[1:0])
            0: state[5 +: 37] <= {d[4:0], d};
            1: state[53 +: 37] <= {d[4:0], d};
            2: state[101 +: 37] <= {d[4:0], d};
            3: state[149 +: 37] <= {d[4:0], d};
        endcase
        if (d[6]) state[d[5:0] * 8'd3 +: 8] <= d[15:8];
    end
    cache_slice_reader #(.OFFSET(5)) u0 (.clk(gated_clk), .state(state), .d(d[7:0]), .y(y0));
    cache_slice_reader #(.OFFSET(53)) u1 (.clk(gated_clk), .state(state), .d(d[7:0]), .y(y1));
    cache_slice_reader #(.OFFSET(101)) u2 (.clk(gated_clk), .state(state), .d(d[7:0]), .y(y2));
    cache_slice_reader #(.OFFSET(149)) u3 (.clk(gated_clk), .state(state), .d(d[7:0]), .y(y3));
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
    logic [31:0] chain_a, chain_b, chain_y, chain_expected, chain_salt;
    logic [31:0] random_state = 32'h1badf00d;
    logic [127:0] partial_state = '0;
    logic [31:0] partial_y;
    logic [191:0] slice_state = '0;
    logic [7:0] slice_salt = 0;
    logic [63:0] slice_y0, slice_y1, slice_y2, slice_y3;

    cache_slices slices (.clk(clk), .gated_clk(c0), .d(random_state),
                         .y0(slice_y0), .y1(slice_y1), .y2(slice_y2), .y3(slice_y3));
    always @(posedge c0) if (random_state[7:0] == 8'hff) slice_salt <= random_state[7:0];
    always @(posedge clk) begin
        if (random_state[7]) slice_state <= {6{random_state}};
        else case (random_state[1:0])
            0: slice_state[5 +: 37] <= {random_state[4:0], random_state};
            1: slice_state[53 +: 37] <= {random_state[4:0], random_state};
            2: slice_state[101 +: 37] <= {random_state[4:0], random_state};
            3: slice_state[149 +: 37] <= {random_state[4:0], random_state};
        endcase
        if (random_state[6]) slice_state[random_state[5:0] * 8'd3 +: 8] <= random_state[15:8];
    end

    cache_partial partial (.clk(c0), .a(chain_a), .b(chain_b), .y(partial_y));
    always @(posedge c0 or negedge c0) begin
        if (c0) partial_state[chain_a[3:0] * 8 +: 8] <= chain_a[15:8];
        else partial_state[95:64] <= chain_b;
    end

    cache_parent chain (.clk(clk), .a(chain_a), .b(chain_b), .y(chain_y));
    always @(posedge clk) chain_salt <= chain_b;
    // Hierarchical probe into a cached group's internals (the real-core probe
    // pattern): must see every update and must not disable caching model-wide.
    logic [31:0] probe_first, probe_salt;
    always_comb probe_first = chain.first;
    always_comb probe_salt = chain.child.salt;
    assign chain_expected = ((((chain_a + 32'd13) * 32'd17)
                              ^ ((chain_b ^ chain_salt) * 32'd29)) + 32'd7) ^ (chain_a * 32'd31);

    always @(negedge clk) begin
        random_state <= {random_state[30:0], random_state[31] ^ random_state[21]
                                            ^ random_state[1] ^ random_state[0]};
        if ((cyc % 4) == 0) chain_a <= random_state;
        if ((cyc % 7) == 0) chain_b <= random_state ^ 32'hffff0000;
    end

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
        chain_a = 0;
        chain_b = 0;
    end

    always @(posedge clk) begin
        cyc <= cyc + 1;
        if (cyc > 1 && (slice_y0 !== (64'(slice_state[5 +: 37]) ^ {56'd0, slice_salt})
                    || slice_y1 !== (64'(slice_state[53 +: 37]) ^ {56'd0, slice_salt})
                    || slice_y2 !== (64'(slice_state[101 +: 37]) ^ {56'd0, slice_salt})
                    || slice_y3 !== (64'(slice_state[149 +: 37]) ^ {56'd0, slice_salt}))) begin
            $display("%%Error: stale packed slice cycle=%0d", cyc);
            $stop;
        end
        if (cyc > 1 && partial_y !== (partial_state[31:0] ^ partial_state[63:32]
                                      ^ partial_state[95:64] ^ partial_state[127:96] ^ chain_b)) begin
            $display("%%Error: lost partial-write invalidation cycle=%0d got=%h expected=%h state=%h b=%h",
                     cyc, partial_y, partial_state[31:0] ^ partial_state[63:32]
                     ^ partial_state[95:64] ^ partial_state[127:96] ^ chain_b, partial_state, chain_b);
            $stop;
        end
        if (cyc > 1 && (probe_first !== chain_a + 32'd13 || probe_salt !== chain_salt)) begin
            $display("%%Error: hierarchical probe stale cycle=%0d first=%h salt=%h", cyc,
                     probe_first, probe_salt);
            $stop;
        end
        if (cyc > 1 && chain_y !== chain_expected) begin
            $display("%%Error: stale execution path cycle=%0d got=%h expected=%h",
                     cyc, chain_y, chain_expected);
            $stop;
        end
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
        end
        if (cyc == 1000) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
