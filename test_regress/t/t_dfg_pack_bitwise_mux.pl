#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Check DFG bitwise 2-way mux packing
# Copyright 2026 Etienne Cimon
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);
compile(verilator_flags2 => ["--stats", "--debug-check", "-fdfg-peephole-pack-bitwise-mux"]);
file_grep($Self->{stats}, qr/DFG\s+pre inline packed bitwise muxes\s+[2-9]\d*/);
execute(check_finished => 1);
ok(1);
1;
