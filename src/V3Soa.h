// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Packed arrays accessed per element -> unpacked tables
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

#ifndef VERILATOR_V3SOA_H_
#define VERILATOR_V3SOA_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Soa final {
public:
    // Rewrite packed arrays that are only indexed by element into unpacked
    // element tables, and mark the counted clocked loops that walk them so
    // V3Unroll leaves those loops rolled.
    static void soaAll(AstNetlist* nodep);
};

#endif
