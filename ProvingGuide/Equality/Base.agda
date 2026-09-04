module ProvingGuide.Equality.Base where

open import Agda.Primitive

infix 4 _≡_
data _≡_ {ℓ : Level} {X : Set ℓ} : X → X → Set ℓ where
  refl : {a : X} → a ≡ a


