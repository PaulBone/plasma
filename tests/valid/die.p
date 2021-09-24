/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Die

entrypoint
func main() uses IO -> Int {
    Builtin.die("Dieing")
    
    /*
     * Return shouldn't be necessary since die won't fall-through.  However
     * Plasma doesn't yet understand exceptions and we'll implement that once
     * exceptions exist.
     */
    return 0
}

