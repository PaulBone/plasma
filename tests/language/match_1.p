/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Match_1

entrypoint
func main() uses IO -> Int {
    print!("fib1(16) = " ++ int_to_string(fib1(16)) ++ "\n")
    print!("fib2(16) = " ++ int_to_string(fib2(16)) ++ "\n")
    print!("fib3(16) = " ++ int_to_string(fib3(16)) ++ "\n")
    print!("fib4(16) = " ++ int_to_string(fib4(16)) ++ "\n")
    test5!()
    test6!()
    return 0
}

func fib1(n : Int) -> Int {
    match (n) {
        0 -> {
            return 1
        }
        1 -> {
            return 1
        }
        var m -> {
            return fib1(m-1) + fib1(m-2)
        }
    }
}

func fib2(n : Int) -> Int {
    var r
    match (n) {
        0 -> {
            r = 1
        }
        1 -> {
            r = 1
        }
        var m -> {
            r = fib2(m-1) + fib2(m-2)
        }
    }

    return r
}

func fib3(n : Int) -> Int {
    var r
    match (n) {
        0 -> {
            r = 1
        }
        1 -> {
            var m = 1
            r = m
        }
        var m -> {
            r = fib3(m-1) + fib3(m-2)
        }
    }

    return r
}

func fib4(n : Int) -> Int {
    var r
    match (n) {
        0 -> {
            r = 1
        }
        1 -> {
            var m = "fish"
            r = 1
        }
        var m -> {
            r = fib4(m-1) + fib4(m-2)
        }
    }

    return r
}

func test5() uses IO {
    print!(beer(10) ++ "\n")
    print!(beer(5) ++ "\n")
    print!(beer(1) ++ "\n")
    print!(beer(0) ++ "\n")
    print!(beer(-1) ++ "\n")
}

/* 
 * Test switches that provide multiple values
 * Test wildcard matches
 * Test negative patterns
 */
func beer(n : Int) -> String {
    var beer_str
    var panic
    match (n) {
        -1 -> {
            beer_str = "You owe someone a beer!"
            panic = "Better repay them!"
        }
        0 -> {
            beer_str = "No more beer!"
            panic = "PANIC!"
        }
        1 -> {
            beer_str = "Only one beer left."
            panic = "worry..."
        }
        _ -> {
            beer_str = int_to_string(n) ++ " more beers left."
            panic = ""
        }
    }

    return beer_str ++ " " ++ panic
}

func test6() uses IO {
    func t(a : Int) -> String {
        var b
        var str
        match (a) {
            0 -> {
                b = 0
                str = "zero"
            }
            // Matches anything and binds it to b which is visible outside.
            b -> {
                str = "more"
            }
        }

        return int_to_string(b) ++ " is " ++ str ++ "\n"
    }

    print!(t(0))
    print!(t(5))
}

