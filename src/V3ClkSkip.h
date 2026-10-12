// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Skip stable per-instance combinational code
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3CLKSKIP_H_
#define VERILATOR_V3CLKSKIP_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3ClkSkip final {
public:
    // After scheduling, guard combo that still runs when an instance's own
    // inputs did not change. Clocked regions stay on their edge trigger.
    static void clkSkipAll(AstNetlist* nodep);
};

#endif
