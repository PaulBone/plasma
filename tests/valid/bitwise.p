/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

/*
 * These are not the final names of the bitwise operators.  They will
 * probably be renamed and placed in a module.
 */

module Bitwise

export
func main() uses IO -> Int {
    print!("1 << 8 = " ++ int_to_string(lshift_int(1, 8)) ++ "\n")
    print!("21 >> 2 = " ++ int_to_string(rshift_int(21, 2)) ++ "\n")
    print!("~7 = " ++ int_to_string(comp_int(7)) ++ "\n")

    return 0
}

