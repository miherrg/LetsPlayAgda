module ProgrammingGuide.boolean where

data Bool : Set where
  false : Bool
  true  : Bool

our-first-constant : Bool
our-first-constant = true

idBool : Bool -> Bool
idBool x = x

not : Bool -> Bool
not false = true
not true = false

example-run : Bool
example-run = not our-first-constant
