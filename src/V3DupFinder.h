// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash AST trees to find duplicates
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
//  Datastructure for finding duplicate AstNode trees via hashing
//
//*************************************************************************

#ifndef VERILATOR_V3DUPFINDER_H_
#define VERILATOR_V3DUPFINDER_H_
#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3Hasher.h"

#include <map>
#include <memory>
#include <unordered_map>

//============================================================================

struct V3DupFinderUserSame {
    // Functor for V3DupFinder::findDuplicate
    virtual bool isSame(AstNode*, AstNode*) = 0;
    V3DupFinderUserSame() = default;
    virtual ~V3DupFinderUserSame() = default;
};

// Hash from node hash to node pointer. Lookup is O(1). When several nodes
// share a hash, the earliest inserted match wins, which is the order the
// old tree map produced.
class V3DupFinder final : private std::unordered_multimap<V3Hash, AstNode*> {
    using Super = std::unordered_multimap<V3Hash, AstNode*>;

    // MEMBERS
    const V3Hasher* const m_hasherp = nullptr;  // Pointer to owned hasher
    const V3Hasher& m_hasher;  // Reference to hasher
    std::unordered_map<const AstNode*, uint64_t> m_order;  // Insertion sequence
    uint64_t m_next = 1;

public:
    // CONSTRUCTORS
    V3DupFinder()
        : m_hasherp{new V3Hasher}
        , m_hasher{*m_hasherp} {}
    explicit V3DupFinder(const V3Hasher& hasher)
        : m_hasher{hasher} {}
    ~V3DupFinder() {
        if (m_hasherp) delete m_hasherp;
    }

    // METHODS

    // Expose minimal set of superclass interface
    using Super::begin;
    using Super::cbegin;
    using Super::cend;
    using Super::clear;
    using Super::const_iterator;
    using Super::empty;
    using Super::end;
    using Super::iterator;
    using Super::size_type;

    // Insert node into data structure. unordered_multimap::emplace returns
    // the iterator itself (not a pair); callers erase that iterator.
    iterator insert(AstNode* nodep) {
        m_order.emplace(nodep, m_next++);
        return emplace(m_hasher(nodep), nodep);
    }

    iterator erase(iterator it) {
        m_order.erase(it->second);
        return Super::erase(it);
    }

    // Erase node from data structure
    size_type erase(AstNode* nodep);

    // Return duplicate, if one was inserted, with optional user check for sameness
    iterator findDuplicate(AstNode* nodep, V3DupFinderUserSame* checkp = nullptr);

    // Dump for debug
    void dumpFile(const string& filename, bool tree);
    void dumpFilePrefixed(const string& nameComment, bool tree = false);
};

#endif  // Guard
