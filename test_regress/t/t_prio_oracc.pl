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

compile(
    # Small unroll limit keeps every test loop rolled until V3Prio sees it;
    # at the default 64 only the 72-bit loop would survive that long.
    # -fprio-oracc exercises the decoupled entry point; -fprio covers the
    # same transform inside prioAll.
    verilator_flags2 => ["--stats", "--debug-check", "-fprio-oracc", "--unroll-count", "8"],
    );

if ($Self->{vlt_all}) {
    # m2t16 + m2t48 + m2t72 functions and the t32 always_comb loop lower to
    # a one-hot guard plus ctz; the descending and i+1 loops must not count.
    file_grep($Self->{stats}, qr/Optimizations, Priority encoders lowered\s+(\d+)/, 4);
    my @files = glob_all("$Self->{obj_dir}/$Self->{vm_prefix}__*.cpp");
    file_grep_any(\@files, qr/VL_CTZ_W/);
    file_grep_any(\@files, qr/VL_ONEHOT0_W/);
    file_grep_any(\@files, qr/VL_CTZ_[IQ]/);
    file_grep_any(\@files, qr/VL_ONEHOT0_[IQ]/);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
