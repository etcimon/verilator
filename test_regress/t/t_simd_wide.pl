#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2023 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

# The kernels pick their width from the -march the model is compiled with; the
# driver's default flags leave that to the host compiler. VL_SIMD_PREFER_512 and
# VL_DISABLE_SIMD are exercised by the leaf review, not here.
compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--exe $Self->{t_dir}/$Self->{name}.cpp"],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
