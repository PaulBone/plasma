/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Builtin04String

/*
 * This test should be kept up-to-date with the documentation for the
 * builtins in docs/plasma_ref.txt
 */
entrypoint
func main() uses IO -> Int {

    // Show that we can name the type and constructor.
    func name_some_types(s : String, c : CodePoint, cc : CodepointCategory) ->
        StringPos
    {
        return string_begin(s)
    }

    // Concat
    print!("aaa" ++ "bbb" ++ "\n")
    print!(Builtin.string_concat("abc", "123") ++ "\n")

    // string_begin and string_end
    var s = "Hello world"
    var begin = string_begin(s)
    var end = string_end(s)

    // Strpos stuff.
    var moved = repeat(6, strpos_forward, begin)
    var moved2 = strpos_backward(moved)

    // substring
    var s2 = string_substring(moved, end)

    // String equals
    print!("world == " ++ s2 ++ " = " ++
        bool_to_string(string_equals("world", s2)) ++ "\n")

    var mc1 = strpos_prev(moved)
    var mc2 = strpos_next(moved2)

    match (mc1) {
        None -> {
            print!("Failed to get prev character from moved\n")
        }
        Some(var c1) -> {
            match (mc2) {
                None -> {
                    print!("Failed to get next character from moved2\n")
                }
                Some(var c2) -> {
                    // codepoint category 
                    var cl1 = codepoint_category(c1)
                    var cl2 = codepoint_category(c2)
                    print!("cl1 is " ++ category_string(cl1) ++ "\n")
                    print!("cl2 is " ++ category_string(cl2) ++ "\n")
                }
            }
        }
    }

    print!("Check codepoint_to_number('a') = " ++
        int_to_string(codepoint_to_number("a")) ++ "\n")
    print!("Check int_to_codepoint(112) = " ++
        codepoint_to_string(Builtin.int_to_codepoint(112)) ++ "\n")
 
    return 0
}

func category_string(c : CodepointCategory) -> String {
    return match (c) {
        Whitespace -> "Whitespace"
        Other -> "Other"
    }
}

func repeat(num : Int, f : func('x) -> 'x, x : 'x) -> 'x {
    if (num > 0) {
        return repeat(num - 1, f, f(x))
    } else {
        return x
    }
}

