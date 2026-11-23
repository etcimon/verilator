#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Only fuse the complete, privately consumed transpose
# Copyright 2026 Etienne Cimon
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);
# Preserve the small matrix until DFG matching; the default field splitter
# legitimately splits this 81-bit near-miss fixture before DFG sees it.
compile(verilator_flags2 => ["--stats", "--debug-check", "-fno-field-split", "-fno-split-plan",
                             "-fdfg-peephole-fuse-transpose-reductions"]);
file_grep($Self->{stats}, qr/DFG\s+pre inline fused transposes\s+(\d+)/, 1);
execute(check_finished => 1);
ok(1);
1;
