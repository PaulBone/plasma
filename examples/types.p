// vim: ft=plasma
// This is free and unencumbered software released into the public domain.
// See ../LICENSE.unlicense

module Types 

/*
 * This example doesn't yet compile.  The uncommented code requires a type
 * alias for Number and the module system and a Set module.
 */

// We can define our own types.

// A simple enum
type Suit = Hearts | Diamonds | Spades | Clubs
type Number = Ace
            | One
            | Two
            | Three
            | Four
            | Five
            | Six
            | Seven
            | Eight
            | Nine
            | Ten
            | Jack
            | Queen
            | King

// A structure: a single constructor with fields.
type PlayingCard = Card ( suit : Suit, number : Number )

// A combination of the above, a PlayingCard is either an ordinary card or a
// joker.  An orderinary card has fields.
type PlayingCardOrJoker = OrdinaryCard ( suit : Suit, number : Number )
                        | Joker

// Types are polymorphic, they may take type parameters.
type Tree('k, 'v) = EmptyTree
                  | Node (
                      key     : 'k,
                      value   : 'v,
                      left    : Tree('k, 'v),
                      right   : Tree('k, 'v)
                  )

// Test that module qualifiers work on type expressions.
import Set

type MyType = MyConstr (
                 field  : Set.Set(Int)
              )

//
// Type Aliases
//
//
//# A type alias, ID is now another word for Int.
//type_alias ID = Int
//
//# It's often more useful to alias something more complex.
//type_alias Name = String
//type_alias NameMap = Map(ID, Name)
//
//# Type aliases can take parameters:
//type_alias IDMap(x) = Map(ID, x)
//


// Empty main function.
entrypoint
func main() uses IO -> Int {
    return 0
}

