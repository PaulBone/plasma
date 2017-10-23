
module Return_1 

import io

func foo() -> Int uses IO {
    # The arity of the expression matches, but there's no explicit return
    # statement.  This was silently accepted as correct.
    return1()
}

# The same but when there's no statements at all.
func bar() -> Int { }

func return1() -> Int {
    return 3
}
