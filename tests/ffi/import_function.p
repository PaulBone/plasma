/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module ImportFunction

pragma foreign_include("import_function.h")

func getpid() -> Int
    foreign(my_getpid)

func foo() uses IO
    foreign(foo)

entrypoint
func hello() uses IO -> Int {
    print!("Hello world\n")

    var pid = getpid!()
    print!("# My pid is " ++ int_to_string(pid) ++ "\n")

    var pid2 = getpid!()
    if (pid == pid2) {
        print!("My pid didn't change\n")
    } else {
        print!("My pid changed, that's weird\n")
    }

    print!("Doing another foreign call\n")
    foo!()
    print!("done\n")

    return 0
}

