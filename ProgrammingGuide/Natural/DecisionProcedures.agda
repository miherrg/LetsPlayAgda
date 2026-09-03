module ProgrammingGuide.Natural.DecisionProcedures where

  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit
  open import ProgrammingGuide.boolean

  eq? : ℕ → ℕ → Bool
  eq? zero zero = true
  eq? (succ n) zero = false
  eq? zero (succ m) = false
  eq? (succ n) (succ m) = eq? n m

  ≤? : ℕ → ℕ → Bool
  ≤? m n = eq? (m ∸ n) 0

  <? : ℕ → ℕ → Bool
  <? m n = ≤? (succ m) n

  even? : ℕ → Bool
  even? zero = true
  even? 1 = false
  even? (succ (succ n)) = even? n

  odd? : ℕ → Bool
  odd? n = not (even? n)


