// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Set dirty bits on stores to hybrid cut signals
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

#ifndef VERILATOR_V3DIRTY_H_
#define VERILATOR_V3DIRTY_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Dirty final {
public:
    // After scheduling, a wide hybrid cut reads its dirty bits instead of
    // comparing the whole vector. This pass sets those bits on each store.
    static void dirtyAll(AstNetlist* nodep);
};

#endif
