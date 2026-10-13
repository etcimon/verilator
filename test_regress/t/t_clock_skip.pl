#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2023 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

# 1,000 cycles at the driver's 10-unit clock period; the default sim_time (1100)
# would time out before the fixture's $finish. _make_main reads $Self directly.
$Self->{sim_time} = 12000;

compile(
    verilator_flags2 => ["--stats", "--debug-check", "-fclock-skip", "-fno-gate", "-fno-dfg"],
    );

if ($Self->{vlt}) {
    file_grep($Self->{stats}, qr/Optimizations, Clock skip scopes\s+[1-9]\d*/);
    file_grep($Self->{stats}, qr/Optimizations, Clock skip invalidation edges\s+[1-9]\d*/);
    file_grep($Self->{stats}, qr/Optimizations, Clock skip disjoint subscriptions\s+[1-9]\d*/);
    file_grep_not($Self->{stats}, qr/Optimizations, Clock skip unsupported model/);
    file_grep($Self->{stats}, qr/Optimizations, Trigger word tests\s+[1-9]\d*/);
    my @files = glob_all("$Self->{obj_dir}/$Self->{vm_prefix}___024root__DepSet_*.cpp");
    file_grep_any(\@files, qr/__Vclkskip/);
} elsif ($Self->{vltmt}) {
    file_grep($Self->{stats}, qr/Optimizations, Clock skip unsupported model\s+(\d+)/, 1);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
