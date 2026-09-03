module HigherOrder where

open import boolean
open import operators

is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = (f true) and (f false)

is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = (is-tautology₁ (f true)) and (is-tautology₁ (f false))

Endo : Set → Set
Endo X = X → X

infixr 9 _∘_
_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) = λ x → f (g x)
