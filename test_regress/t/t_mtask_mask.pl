#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2023 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vltmt => 1);

compile(
    verilator_flags2 => ["--stats", "-no-threads-coarsen"],
    threads => 2,
    );

if ($Self->{vltmt}) {
    file_grep($Self->{stats}, qr/Scheduling, MTask done mask words\s+(\d+)/, 3);
    my @files = glob_all("$Self->{obj_dir}/$Self->{vm_prefix}*.cpp");
    file_grep_any(\@files, qr/__Vm_mtask_done__nba\.wait\(/);
    file_grep_any(\@files, qr/__Vm_mtask_done__nba\.signal\(/);
    foreach my $file (@files) {
        file_grep_not($file, qr/signalUpstreamDone/);
    }
}

execute(
    check_finished => 1,
    );

ok(1);
1;
