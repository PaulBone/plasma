/*
 * Plasma garbage collector memory layout
 * vim: ts=4 sw=4 et
 *
 * Copyright (C) 2019 Plasma Team
 * Distributed under the terms of the MIT license, see ../LICENSE.code
 */

#ifndef PZ_GC_LAYOUT_H
#define PZ_GC_LAYOUT_H

#include "pz_gc.h"
#include "pz_gc.impl.h"

namespace pz {

/*
 * The heap is made out of little blocks and big blocks.  A big block
 * contains multiple little blocks, which each contain multiple cells.
 */

class Cell {
  public:
    uint8_t* bits() const;
    LBlock* lblock() const;
    size_t size() const;
    void** pointer() {
        return reinterpret_cast<void**>(this);
    }

    bool is_allocated() const;
    bool is_marked() const;
    void mark();
};

/*
 * Little blocks - LBlock
 *
 * These must be a power-of-two and mmap must align to them. 4K is the
 * default.
 */
static const unsigned GC_LBLOCK_LOG = 13;
static const size_t GC_LBLOCK_SIZE = 1 << (GC_LBLOCK_LOG - 1);
static const size_t GC_LBLOCK_MASK = ~(GC_LBLOCK_SIZE - 1);
static const unsigned GC_MIN_CELL_SIZE = 2;
static const unsigned GC_CELLS_PER_LBLOCK = GC_LBLOCK_SIZE /
    (GC_MIN_CELL_SIZE * WORDSIZE_BYTES);

class LBlock {
  private:
    struct Header {
        // Word size of cells or zero if this LBlock is unused.
        size_t    cell_size;
        // Really a bytemap.
        uint8_t   bitmap[GC_CELLS_PER_LBLOCK];

        explicit Header(size_t cell_size_) :
            cell_size(cell_size_) {}
        Header() {}
    };

    Header m_header;

    static constexpr size_t HEADER_BYTES =
        RoundUp<size_t>(sizeof(m_header), WORDSIZE_BYTES);
    static constexpr size_t PAYLOAD_BYTES =
        GC_LBLOCK_SIZE - HEADER_BYTES;

    alignas(WORDSIZE_BYTES)
    uint8_t     m_bytes[PAYLOAD_BYTES];

  public:
    explicit LBlock(size_t cell_size_) : m_header(cell_size_)
    {
        assert(cell_size_ >= GC_MIN_CELL_SIZE);
        memset(m_header.bitmap, 0, GC_CELLS_PER_LBLOCK * sizeof(uint8_t));
    }

    // This constructor won't touch any memory and can be used to construct
    // uninitialised LBlocks within BBlocks.
    LBlock() {}

    LBlock(const LBlock&) = delete;
    void operator=(const LBlock&) = delete;

    // Size in words.
    size_t size() const { return m_header.cell_size; }
    unsigned num_cells() const {
        unsigned num = PAYLOAD_BYTES / (size() * WORDSIZE_BYTES);
        assert(num <= GC_CELLS_PER_LBLOCK);
        return num;
    }

    bool is_in_payload(const void *ptr) const;
    bool is_valid_address(const void *ptr) const;

    unsigned index_of(const void *ptr) const;
    Cell* cell(unsigned index);

    const uint8_t * cell_bits(unsigned index) const;
    uint8_t * cell_bits(unsigned index);

    bool is_empty() const;
    bool is_full() const;
    bool is_in_use() const { return m_header.cell_size != 0; }

    void sweep();

    Cell* allocate_cell();
};

static_assert(sizeof(LBlock) == GC_LBLOCK_SIZE);

/*
 * Big blocks - BBlocks
 *
 * GC_BBLOCK_SIZE is also a power of two and is therefore a multiple of
 * GC_LBLOCK_SIZE.  4MB is the default.
 */
static const unsigned GC_BBLOCK_LOG = 23;
static const size_t GC_BBLOCK_SIZE = 1 << (GC_BBLOCK_LOG - 1);
static const size_t GC_LBLOCK_PER_BBLOCK =
        (GC_BBLOCK_SIZE / GC_LBLOCK_SIZE) - 1;

class BBlock {
  public:
    uint32_t    m_wilderness;

    alignas(GC_LBLOCK_SIZE)
    LBlock      m_blocks[GC_LBLOCK_PER_BBLOCK];

  public:
    BBlock() : m_wilderness(0) { }

    BBlock(const BBlock&) = delete;
    void operator=(const BBlock&) = delete;

    LBlock* next_block();

    bool is_empty() const;

    /*
     * True if this pointer lies within this bblock, even if unallocated.
     *
     * TODO: True if this pointer lies within an allocated lblock.
     */
    bool contains_pointer(void *ptr) const {
        return ptr >= &m_blocks[0] && ptr < &m_blocks[GC_LBLOCK_PER_BBLOCK];
    };

    void sweep();
};

static_assert(sizeof(BBlock) == GC_BBLOCK_SIZE);

static const size_t GC_MAX_HEAP_SIZE = GC_BBLOCK_SIZE;
static const size_t GC_HEAP_SIZE = 64*GC_LBLOCK_SIZE;

static_assert(GC_BBLOCK_SIZE > GC_LBLOCK_SIZE);
static_assert(GC_MAX_HEAP_SIZE >= GC_BBLOCK_SIZE);
static_assert(GC_MAX_HEAP_SIZE >= GC_HEAP_SIZE);

} // namespace pz

#endif // ! PZ_GC_LAYOUT_H