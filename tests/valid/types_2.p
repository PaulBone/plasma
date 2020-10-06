/*
 * vim: ft=plasma
 * This is free and unencumbered software released into the public domain.
 * See ../LICENSE.unlicense
 */

module Types_2

// Simple enum
type Suit = Hearts | Diamonds | Spades | Clubs
type RedSuit = Hearts | Diamonds

entrypoint
func main() uses IO -> Int {
    print!("Queen of " ++ suit_str(Hearts) ++ "\n")
    print!("Ace of " ++ suit_str(Spades) ++ "\n")
    return 0
}

func suit_str(s : Suit) -> String {
    match (s) {
        Hearts -> { return "Hearts" }
        Diamonds -> { return "Diamonds" }
        Spades -> { return "Spades" }
        Clubs -> { return "Clubs" }
    }
}



