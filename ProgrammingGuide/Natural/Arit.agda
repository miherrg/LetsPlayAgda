module ProgrammingGuide.Natural.Arit where

open import ProgrammingGuide.Natural.Base

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)

twice : (x : ℕ) → ℕ
twice x = x + x

half : (n : ℕ) → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = half n + 1

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
a ∸ zero = a
zero ∸ succ b = zero
succ a ∸ succ b = a ∸ b

infixl 7 _·_
_·_ : ℕ → ℕ → ℕ
zero · b = zero
succ a · b = a · b + b

infixr 8 _²
_² : ℕ → ℕ
x ² = x · x

infixr 8 _^_ -- Como estamos usando infix right, asocia a dcha, es decir 2 ^ 3 ^ 2 ≠ 64 si no 512
_^_ : ℕ → ℕ → ℕ
a ^ zero = 1
a ^ succ b = a · a ^ b

max : ℕ → ℕ → ℕ
max zero b = b
max a zero = a
max (succ a) b = succ (max a (pred b))

example-computation : ℕ
example-computation = max 13 5
