// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Mark combinational-cycle variables for splitting
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

#ifndef VERILATOR_V3SPLITPLAN_H_
#define VERILATOR_V3SPLITPLAN_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3SplitPlan final {
public:
    // Before V3SplitVar, mark internal variables that sit on a combinational
    // cycle. The splitter then consumes those marks in the same run.
    static void splitPlanAll(AstNetlist* nodep);
};

#endif
