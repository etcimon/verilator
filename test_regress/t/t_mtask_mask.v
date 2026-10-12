// DESCRIPTION: Verilator: MTask predecessor bitmask
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Enough independent lanes that the done-mask needs more than one word,
// plus a join that has to wait for lanes running on the other thread.
module t (/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    localparam int N = 70;
    integer cyc;
    logic [31:0] x[N];
    logic [31:0] sum;

    initial begin
        cyc = 0;
        sum = 0;
        for (int i = 0; i < N; i++) x[i] = 0;
    end

    for (genvar i = 0; i < N; i++) begin : g
        always @(posedge clk) x[i] <= x[i] + 32'(i) + 32'd1;
    end

    always @(posedge clk) begin
        logic [31:0] acc;
        acc = 0;
        for (int i = 0; i < N; i++) acc += x[i];
        sum <= acc;
    end

    always @(posedge clk) begin
        cyc <= cyc + 1;
        // At this edge, each lane has been incremented `cyc` times and
        // `sum` still holds the previous total.
        if (cyc == 4) begin
            if (x[0] !== 32'd4 || x[N - 1] !== 32'd4 * N) begin
                $display("%%Error: lane x0=%0d xN=%0d", x[0], x[N - 1]);
                $stop;
            end
            if (sum !== 32'd3 * N * (N + 1) / 2) begin
                $display("%%Error: sum=%0d", sum);
                $stop;
            end
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
