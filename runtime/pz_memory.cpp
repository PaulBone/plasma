/*
 * Plasma large memory region allocation
 * vim: ts=4 sw=4 et
 *
 * Copyright (C) 2021 Plasma Team
 * Distributed under the terms of the MIT license, see ../LICENSE.code
 */

#include "pz_common.h"

#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>

#include "pz_memory.h"

const static size_t PAGE_SIZE = [] {return sysconf(_SC_PAGESIZE); }();

bool
MemoryBase::allocate(size_t size, bool guarded) {
    size_t mmap_size = size;
    if (guarded) {
        mmap_size += PAGE_SIZE*2;
    }

    void *ptr = mmap(NULL, mmap_size, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

    if (MAP_FAILED == ptr) {
        return false;
    }

    if (guarded) {
        void * guard_address_1 = ptr;
        void * guard_address_2 = reinterpret_cast<void*>(
            reinterpret_cast<uintptr_t>(ptr) + PAGE_SIZE + size);
        ptr = reinterpret_cast<void*>(
                reinterpret_cast<uintptr_t>(ptr) + PAGE_SIZE);

        if (0 != mprotect(guard_address_1, PAGE_SIZE, PROT_NONE)) {
            return false;
        }
        if (0 != mprotect(guard_address_2, PAGE_SIZE, PROT_NONE)) {
            return false;
        }
    }

    m_pointer = ptr;
    m_size = size;
    m_has_guards = guarded;
    return true;
}

bool
MemoryBase::release() {
    if (m_pointer) {
        void *ptr = m_pointer;
        size_t size = m_size;
        if (m_has_guards) {
            ptr = reinterpret_cast<void*>(
                    reinterpret_cast<uintptr_t>(m_pointer) - PAGE_SIZE);
            size = m_size + PAGE_SIZE*2;
        }
        if (-1 == munmap(ptr, size)) {
            perror("munmap");
            return false;
        }
        m_pointer = nullptr;
    }

    return true;
}

void
MemoryBase::forget() {
    m_pointer = nullptr;
}

