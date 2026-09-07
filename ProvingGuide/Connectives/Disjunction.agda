module ProvingGuide.Connectives.Disjunction where

  open import ProvingGuide.Negation

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
