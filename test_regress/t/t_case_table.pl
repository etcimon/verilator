#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ["--stats"],
    );

if ($Self->{vlt_all}) {
    # Six cases qualify for ConstPool lookup tables: blocking assigns with
    # default (a, c), function return arms (ftable), full coverage without
    # default (d), multi-label items (e), and nonblocking arms (q).
    file_grep($Self->{stats}, qr/Optimizations, Cases to lookup tables\s+(\d+)/i, 6);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
