#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Test sink-domain clock-gated NBA comb deferral (ST and MT)
# Copyright 2026 Etienne Cimon
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

$Self->{sim_time} = 20000;

compile(
    verilator_flags2 => ["--stats", "--debug-check", "-fclock-skip-sink"],
    );

if ($Self->{vlt} || $Self->{vltmt}) {
    file_grep($Self->{stats}, qr/Optimizations, Clock skip sink groups\s+[1-9]\d*/);
    file_grep($Self->{stats}, qr/Optimizations, Clock skip sink deferred calls\s+[1-9]\d*/);
    file_grep_not($Self->{stats}, qr/Optimizations, Clock skip sink unsupported model/);
    my @files = glob_all("$Self->{obj_dir}/$Self->{vm_prefix}___024root__DepSet_*.cpp");
    file_grep_any(\@files, qr/__Vclkskip_sink_d/);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
