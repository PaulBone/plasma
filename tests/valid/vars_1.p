/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Vars_1

entrypoint
func main() uses IO -> Int {
    // We can assign to _ as many times as we want.
    _ = foo(1)
    _, var x = bar(3)
    _ = foo(2)
    var y, _ = bar(4)

    print!("x, y: " ++ int_to_string(x) ++ ", " ++ int_to_string(y) ++ "\n")
    print!("z: " ++ int_to_string(baz(x, y, x+y)) ++ "\n")

    return 0
}

// Wildcards can appear as function arguments.
func foo(_ : Int) -> Int { return 3 }

func bar(n : Int) -> (Int, Int) { return n - 3, n+2 }

// Wildcards can appear multiple times as function arguments, and also in the
// body:
func baz(_ : Int, _ : Int, c : Int) -> Int {
    _ = foo(c)
    return c*4
}

