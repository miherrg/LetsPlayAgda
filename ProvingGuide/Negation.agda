module ProvingGuide.Negation where

  open import ProgrammingGuide.Natural.Base
  open import ProvingGuide.EvenOdd

  data ⊥ : Set where

  infix 3 ¬_
  ¬_ : Set → Set
  ¬ P = (P → ⊥)

  one-not-even : ¬ Even 1
  one-not-even ()

  even-and-odd : {a : ℕ} → Even a → Odd a → ⊥
  even-and-odd (step-even p) (step-odd q) = even-and-odd p q

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  contradiction : {A : Set} → A → ¬ A → ⊥
  contradiction p not-p = not-p p


  dni : {A : Set} → A → ¬ ¬ A
  dni p q = q p

  contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
  contraposition p q r = q (p r)
