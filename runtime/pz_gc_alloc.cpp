/*
 * Plasma garbage collector collection procedures 
 * vim: ts=4 sw=4 et
 *
 * Copyright (C) 2019 Plasma Team
 * Distributed under the terms of the MIT license, see ../LICENSE.code
 */

#include "pz_common.h"

#include <string.h>

#include "pz_util.h"

#include "pz_gc.h"
#include "pz_gc_util.h"

#include "pz_gc.impl.h"
#include "pz_gc_layout.h"

namespace pz {

void *
Heap::alloc(size_t size_in_words, const GCCapability &gc_cap)
{
    assert(size_in_words > 0);

    void *cell;
#ifdef PZ_DEV
    if (m_options.gc_zealous() &&
        gc_cap.can_gc() &&
        !is_empty())
    {
        // Force a collect before each allocation in this mode.
        cell = NULL;
    } else
#endif
    {
        cell = try_allocate(size_in_words);
    }
    if (cell == NULL && gc_cap.can_gc()) {
        collect(&gc_cap.tracer());
        cell = try_allocate(size_in_words);
        if (cell == NULL) {
            fprintf(stderr, "Out of memory, tried to allocate %lu bytes.\n",
                        size_in_words * WORDSIZE_BYTES);
            abort();
        }
    }

    return cell;
}

void *
Heap::alloc_bytes(size_t size_in_bytes, const GCCapability &gc_cap) {
    size_t size_in_words = AlignUp(size_in_bytes, WORDSIZE_BYTES) /
        WORDSIZE_BYTES;

    return alloc(size_in_words, gc_cap);
}

void *
Heap::try_allocate(size_t size_in_words)
{
    if (size_in_words < GC_MIN_CELL_SIZE) {
        size_in_words = GC_MIN_CELL_SIZE;
    } else if (size_in_words <= 16) {
        size_in_words = RoundUp(size_in_words, size_t(2));
    } else {
        size_in_words = RoundUp(size_in_words, size_t(4));
    }

    if (size_in_words > LBlock::MAX_CELL_SIZE) {
        fprintf(stderr, "Allocation %ld too big for GC\n", size_in_words);
        abort();
    }

    /*
     * Try the free list
     */
    LBlock *block = get_free_list(size_in_words);
    if (!block) {
        block = allocate_block(size_in_words);
        if (!block) {
            #ifdef PZ_DEV
            if (m_options.gc_trace2()) {
                fprintf(stderr, "Heap full for allocation of %ld words\n",
                        size_in_words);
            }
            #endif
            return nullptr;
        }
    }

    CellPtr cell = block->allocate_cell();

    if (!cell.isValid()) return nullptr;

    #ifdef PZ_DEV
    if (m_options.gc_trace2()) {
        fprintf(stderr, "Allocated %p from free list\n", cell.pointer());
    }
    #endif

    return cell.pointer();
}

LBlock *
Heap::get_free_list(size_t size_in_words)
{
    LBlock **lists = m_free_lists->get_free_list(size_in_words);

    while (*lists && (*lists)->is_full()) {
        *lists = (*lists)->next();
    }

    return *lists;
}

LBlock *
Heap::allocate_block(size_t size_in_words)
{
    LBlock *block;

    if (m_bblock->size() >= m_max_size)
        return nullptr;

    block = m_bblock->free_block();
    if (!block) return nullptr;

    #ifdef PZ_DEV
    if (m_options.gc_trace()) {
        fprintf(stderr, "Allocated new block for %ld cells\n", size_in_words);
    }
    #endif

    new(block) LBlock(m_options, size_in_words);
    m_free_lists->add_free_list(size_in_words, block);

    return block;
}

LBlock*
BBlock::free_block()
{
    for (unsigned i = 0; i < m_wilderness; i++) {
        if (!m_blocks[i].is_in_use()) {
            fprintf(stderr,
                "Running previously-unused code path, " 
                "see https://github.com/PlasmaLang/plasma/issues/191\n");
            return &m_blocks[i];
        }
    }

    if (m_wilderness >= GC_LBLOCK_PER_BBLOCK)
        return nullptr;

    return &m_blocks[m_wilderness++];
}

CellPtr
LBlock::allocate_cell()
{
    assert(is_in_use());

    if (m_header.free_list < 0)
        return CellPtr::Invalid();

    CellPtr cell(this, m_header.free_list);
    assert(!is_allocated(cell));
    m_header.free_list = cell.next_in_list();
    assert(m_header.free_list == Header::EMPTY_FREE_LIST ||
            (m_header.free_list < static_cast<int>(num_cells()) &&
            m_header.free_list >= 0));
    allocate(cell);
    return cell;
}

} // namespace pz
