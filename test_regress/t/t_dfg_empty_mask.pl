#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Check two-state empty-mask reduction group guards
# Copyright 2026 Etienne Cimon
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);
compile(verilator_flags2 => ["--stats", "--debug-check", "-fdfg-peephole-guard-empty-mask"]);
file_grep($Self->{stats}, qr/DFG\s+pre inline empty mask guards\s+(\d+)/, 1);
execute(check_finished => 1);
ok(1);
1;
