module ProvingGuide.Equality.FirstSteps where

  open import ProvingGuide.Equality.Base
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit

  trivial : (a : ℕ) → zero + a ≡ a
  trivial a = refl

  --  nontrivial : (a : ℕ) → a + zero ≡ a
  --  nontrivial zero = refl
  --  nontrivial (succ a) = {!!} Este caso no se puede resolver con refl, pues no se cumple por definición

  lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
  lemma-pred-succ a = refl

