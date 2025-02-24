/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module ExportBadType

type T0 = T0 ( 
    f1 : Int
)

export opaque
type T0a = T0a (
    f1a : Int
)

// Error, T0 is not exported.
export
type T1 = T1 (
    f2 : T0
)

// Error, T0 is not exported.
export
type T2 = T2 (
    f3 : List(T0)
)

// No error, because T3 isn't exported
type T3 = T3 (
    f4 : T0,
    f5 : List(T0)
)

// No error, because the type we refer to is exported abstractly.
export
type T1ia = T1ia (
    f2ia : T0a
)

// No error
export
type T2ia = T2ia (
    f3ia : List(T0a)
)

// No error, because importing libraries don't need to know what this refers
// to.
export opaque
type T1a = T1a (
    f2a : T0
)

export opaque
type T2a = T2a (
    f2a : List(T0)
)

// Error
export
func fun1(a : T0) uses IO {
}

// Error
export
func fun2(a : List(T0)) uses IO { 
}

// No-error
func fun3(a : T0, b : List(T0)) uses IO {
}

// No-error
func fun4(a : T0a, b : List(T0a)) uses IO {
}

