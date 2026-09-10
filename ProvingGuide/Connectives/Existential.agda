module ProvingGuide.Connectives.Existential where

  open import Agda.Primitive
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit
  open import ProvingGuide.EvenOdd
  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.NaturalNumbers

  infixr 4 _,_
  record Σ {ℓ ℓ' : Level} (A : Set ℓ) (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,_
    field
      fst : A
      snd : P fst
  open Σ public

  --- Syntactic Sugar
  infix 2 ∃-syntax
  ∃-syntax : {ℓ ℓ' : Level} {A : Set ℓ} → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
  ∃-syntax = Σ _

  syntax ∃-syntax (λ x → P) = ∃[ x ] P

  even-is-twice : {n : ℕ} → Even n → ∃[ m ] (n ≡ twice m)
  even-is-twice {n} even-n = half n , even-twice even-n
