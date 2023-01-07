/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Closure_Bad_02

export
func main() uses IO -> Int {
    var greeting = "Hello "

    // The compiler crashs when we forget the return type for the closure.
    func hi(name : String) -> String {
        var msg = greeting ++ name ++ "\n"
        return msg
    }

    print!(hi("Paul"))

    // msg wont be available here
    print!(msg)

    return 0
}

