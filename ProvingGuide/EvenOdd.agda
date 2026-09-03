module ProvingGuide.EvenOdd where

  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit

  data Even : ℕ → Set where
    base-even : Even 0
    step-even : {n : ℕ} → Even n → Even (succ (succ n))

  zero-even : Even 0
  zero-even = base-even

  two-even : Even 2
  two-even = step-even (base-even)

  sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
  sum-even base-even     q = q
  sum-even (step-even p) q = step-even (sum-even p q)

  data Odd : ℕ → Set where
    base-odd : Odd 1
    step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

  succ-even : {a : ℕ} → Even a → Odd (succ a)
  succ-even base-even = base-odd
  succ-even (step-even p) = step-odd (succ-even p)

  succ-odd : {a : ℕ} → Odd a → Even (succ a)
  succ-odd base-odd = two-even
  succ-odd (step-odd p) = step-even (succ-odd p)

  data IsZero : ℕ → Set where
    case-zero : IsZero 0

  zero-add-zero-eq-zero : (a b : ℕ) → IsZero a → IsZero b → IsZero (a + b)
  zero-add-zero-eq-zero zero zero aZero bZero = case-zero

  data IsPositive : ℕ → Set where
    case-succ : (n : ℕ) → IsPositive (succ n)

  pos-sum-pos : (a b : ℕ) → IsPositive a → IsPositive (a + b)
  pos-sum-pos (succ a) b aPos = case-succ (a + b)
