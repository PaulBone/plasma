/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module HeirTest

import Heir.Foo
import Heir.Foo.Bar
import Heir.Baz.Troz

entrypoint
func main() uses IO -> Int {
    Heir.Foo.test1!()
    Heir.Foo.Bar.test!()
    Heir.Baz.Troz.test!()

    return 0
}

