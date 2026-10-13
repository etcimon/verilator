#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2026 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ["--stats", "--no-timing"],
);

execute(
    check_finished => 1,
);

# `lanes` is field-split. `wide` is assigned as a whole vector and is not.
file_grep($Self->{stats}, qr/SplitVar,\s+auto field variables\s+(\d+)/i, 1);

ok(1);
1;
