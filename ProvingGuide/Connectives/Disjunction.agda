module ProvingGuide.Connectives.Disjunction where

  open import ProvingGuide.Negation
  open import ProvingGuide.EvenOdd
  open import ProgrammingGuide.Natural.Base
  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.General
  open import ProvingGuide.Equality.NaturalNumbers
  open import ProgrammingGuide.HigherOrder

  infixr 1 _∨_
  data _∨_ (A B : Set) : Set where
    left  : A → A ∨ B
    right : B → A ∨ B

  or-comm : {A B : Set} → A ∨ B → B ∨ A
  or-comm (left A) = right A
  or-comm (right B) = left B

  or-assoc : {A B C : Set} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
  or-assoc (left (left q)) = left q
  or-assoc (left (right q)) = right (left q)
  or-assoc (right p) = right (right p)

  or-elim : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
  or-elim p q (left x) = p x
  or-elim p q (right x) = q x

  or-map : {A A' B B' : Set} → (A → A') → (B → B') → A ∨ B → A' ∨ B'
  or-map p q (left x) = left (p x)
  or-map p q (right x) = right (q x)

  or-idemp : {A : Set} → A ∨ A → A
  or-idemp (left p) = p
  or-idemp (right p) = p

  or-bot : {A : Set} → A ∨ ⊥ → A
  or-bot (left x) = x

  or-neg : {A B : Set} → A ∨ B → ¬ B → A
  or-neg (left x) notB = x
  or-neg (right x) notB = ⊥-elim (notB x)

  even-or-odd : (x : ℕ) → Even x ∨ Odd x
  even-or-odd zero = left base-even
  even-or-odd (succ zero) = right base-odd
  even-or-odd (succ (succ x)) with even-or-odd x
  ... | left p  = left (step-even p)
  ... | right p = right (step-odd p)

  eq? : (a b : ℕ) → (a ≡ b) ∨ ¬ (a ≡ b)
  eq? zero zero = left refl
  eq? zero (succ b) = right λ ()
  eq? (succ a) zero = right λ ()
  eq? (succ a) (succ b) with eq? a b
  ... | left  p = left (cong succ p)
  ... | right p = right λ q → p (succ-injective q)
