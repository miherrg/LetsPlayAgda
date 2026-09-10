module ProvingGuide.Connectives.Conjunction where

  open import Agda.Primitive
  open import ProvingGuide.Connectives.Existential

  infixr 2 _∧_
  _∧_ : {ℓ ℓ' : Level} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
  A ∧ B = Σ A (λ _ → B)

  open ProvingGuide.Connectives.Existential using (fst; snd; _,_) public

  ∧-comm : {A B : Set} → A ∧ B → B ∧ A
  ∧-comm A∧B = (snd A∧B , fst A∧B )
