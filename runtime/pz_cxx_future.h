/*
 * PZ C++ future library functions.
 * vim: ts=4 sw=4 et
 *
 * Copyright (C) 2018-2019 Plasma Team
 * Distributed under the terms of the MIT license, see ../LICENSE.code
 *
 * This file contains library code that has been added to a more recent C++
 * version than the one we've standardised on (C++11) or features that we
 * might reasonably expect to be added to a future version.  If/when we move
 * to a newer standard we can delete entries here and update code as
 * necessary.
 */

#ifndef PZ_CXX_FUTURE_H
#define PZ_CXX_FUTURE_H

#include <string>

/*
 * C++17 libraries don't seem to be on my dev system,
 * other people might also be missing them.  So just implement this
 * ourselves.
 */
template <typename T>
class Optional
{
   private:
    bool m_present;

    /*
     * AlaskanEmily suggested this trick, allocate space for T here and use
     * placement new below so that T's without default constructors can be
     * used.
     */
    static_assert(sizeof(T) >= 1, "T must have non-zero size");
    alignas(alignof(T)) char m_data[sizeof(T)] = {0};

   public:
    constexpr Optional() : m_present(false) {}

    // Implicit constructor
    Optional(const T & val) : m_present(false)
    {
        set(val);
    }

    Optional(const Optional & other) : m_present(false)
    {
        if (other.hasValue()) {
            set(other.value());
        }
    }

    Optional(Optional && other) : m_present(false)
    {
        if (other.hasValue()) {
            set(other.value());
            other.m_present = false;
        }
    }

    ~Optional()
    {
        clear();
    }

    Optional & operator=(const Optional & other)
    {
        if (this != &other && other.hasValue()) {
            set(other.value());
        }

        return *this;
    }

    Optional & operator=(Optional && other)
    {
        if (this != &other && other.hasValue()) {
            set(other.value());
            other.m_present = false;
        }

        return *this;
    }

    static constexpr Optional Nothing()
    {
        return Optional();
    }

    bool hasValue() const
    {
        return m_present;
    }

    void set(const T & val)
    {
        clear();
        new (m_data) T(val);
        m_present = true;
    }

    T & value()
    {
        assert(m_present);
        return reinterpret_cast<T &>(m_data);
    }

    const T & value() const
    {
        assert(m_present);
        return reinterpret_cast<const T &>(m_data);
    }

    T && release()
    {
        assert(m_present);
        m_present = false;
        return std::move(reinterpret_cast<T &>(m_data));
    }

    void clear()
    {
        if (m_present) {
            reinterpret_cast<T *>(m_data)->~T();
        }
    }
};

#endif  // ! PZ_CXX_FUTURE_H
