/*
 * Plasma GC rooting, scopes & C++ allocation utilities
 * vim: ts=4 sw=4 et
 *
 * Copyright (C) 2018-2019 Plasma Team
 * Distributed under the terms of the MIT license, see ../LICENSE.code
 */

#ifndef PZ_GC_UTIL_H
#define PZ_GC_UTIL_H

#include <vector>

#include "pz_gc.h"

namespace pz {

// Forward declarations.
class AbstractGCTracer;

/*
 * This is the base class that the GC will use to determine if its legal to
 * GC.  Do not create subclasses of this, use only AbstractGCTracer.
 */
class GCCapability {
  private:
    Heap *m_heap;

  public:
    GCCapability(Heap *heap) : m_heap(heap) {}

    void * alloc(size_t size_in_words);
    void * alloc_bytes(size_t size_in_bytes);

    Heap * heap() const { return m_heap; }

    virtual bool can_gc() const = 0;

    // Called by the GC if we couldn't allocate this much memory.
    virtual void oom(size_t size_bytes) = 0;

    /*
     * This casts to AbstractGCTracer whenever can_gc() returns true, so it
     * must be the only subclass that overrides can_gc() to return true.
     */
    const AbstractGCTracer& tracer() const;

  protected:
    GCCapability() : m_heap(nullptr) {};
    void set_heap(Heap *heap) {
        assert(!m_heap);
        m_heap = heap;
    }
};

/*
 * AbstractGCTracer helps the GC find the roots, it traces in order to find
 * the GC roots.
 *
 * Roots are traced from two different sources (both use this class).
 * Global roots and thread-local roots.
 */
class AbstractGCTracer : public GCCapability {
  public:
    AbstractGCTracer(Heap *heap) : GCCapability(heap) {}

    virtual bool can_gc() const { return true; }
    virtual void oom(size_t size);
    virtual void do_trace(HeapMarkState*) const = 0;

  private:
    /*
     * A work-around for PZ
     */
    AbstractGCTracer() = default;
    friend class PZ;
};

class NoRootsTracer : public AbstractGCTracer {
  public:
    NoRootsTracer(Heap *heap) : AbstractGCTracer(heap) {}

    virtual void do_trace(HeapMarkState*) const {};
};

/*
 * GCTracer helps the GC find the roots, it traces in order to find the
 * GC roots.
 */
class GCTracer : public AbstractGCTracer {
  private:
    std::vector<void*> m_roots;

    /*
     * This code is currently unused, but it might be useful in the future.
     * Disable it until then so that if/when it gets reused we can review
     * it.
     *
     * Specifically:
     *
     * It could be dangerous to create tracers easilly because doing so
     * might allow the developer to place a /can gc/ scope inside a /no gc/
     * scope.
     */
    GCTracer();

  public:
    void add_root(void *root);

    /*
     * The roots must be removed in LIFO order.
     */
    void remove_root(void *root);

    GCTracer(const GCTracer&) = delete;
    GCTracer& operator=(const GCTracer&) = delete;

    virtual void do_trace(HeapMarkState *state) const;
};

template<typename T>
class Root {
  private:
    T        *m_gc_ptr;
    GCTracer &m_tracer;

  public:
    explicit Root(GCTracer &t) : m_gc_ptr(nullptr), m_tracer(t)
    {
        m_tracer.add_root(&m_gc_ptr);
    }

    Root(const Root& r) :
        m_gc_ptr(r.gc_ptr),
        m_tracer(r.tracer)
    {
        m_tracer.add_root(&m_gc_ptr);
    }

    Root& operator=(const Root& r)
    {
        m_gc_ptr = r.gc_ptr;
    }

    ~Root()
    {
        m_tracer.remove_root(&m_gc_ptr);
    }

    const Root& operator=(T *ptr)
    {
        m_gc_ptr = ptr;
        return *this;
    }

    T* operator->() const
    {
        return m_gc_ptr;
    }

    T* get() const
    {
        return m_gc_ptr;
    }
};

/*
 * Use this RAII class to create scopes where GC is forbidden (the heap will
 * be expanded instead.
 *
 * Allocation is infalliable, even in a NoGCScope (the program will abort
 * rather than return nullptr).  This conforms with C++'s requirements for
 * "new".
 *
 * I'd consider using the C++ new handler within this scope to recover
 * somehow, eg by returning control the the beginning of the scope to allow
 * for a collection or to let the caller abort more gracefully. We'd need to
 * use nothrow to ensure that the constructor isn't called on a null object.
 * It's unlikely to be important in practice so I didn't do it yet.
 */
class NoGCScope : public GCCapability {
  private:
#ifdef PZ_DEV
    // nullptr if this is directly nested within another NoGCScope and we
    // musn't cleanup in the destructor.
    Heap *m_heap;
#endif

  public:
    // The constructor may use the tracer to perform an immediate
    // collection, or if it is a NoGCScope allow the direct nesting.
    NoGCScope(const GCCapability *gc_cap);
    virtual ~NoGCScope();

    virtual bool can_gc() const { return false; }
    virtual void oom(size_t size);
};

class GCNew {
  public:
    /*
     * Operator new is infalliable, it'll abort the program if the
     * GC returns null, which it can only do in a NoGCScope.
     */
    void* operator new(size_t size, GCCapability &gc_cap);
    void* operator new[](size_t size, GCCapability &gc_cap);
    // We don't need a placement-delete or regular-delete because we use GC.
};

} // namespace pz

#endif // ! PZ_GC_UTIL_H
