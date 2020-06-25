/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Arity_HO_1

export
func main() uses IO -> Int {
    // Incorrect arity (type) in function passed to higher order function.
    var f = fst(add4, 3)
    
    return 0
}

func fst(f : func(Int) -> (Int, Int), input : Int) -> Int {
    var a, _ = f(input)
    return a
}

func add4(n : Int) -> Int {
    return n + 4
}

