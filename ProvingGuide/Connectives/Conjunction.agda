module ProvingGuide.Connectives.Conjunction where

  open import Agda.Primitive
  open import ProvingGuide.Connectives.Existential
  open import ProvingGuide.Connectives.Disjunction
  open import ProvingGuide.Negation
  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.NaturalNumbers
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit

  infixr 2 _∧_
  _∧_ : {ℓ ℓ' : Level} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
  A ∧ B = Σ A (λ _ → B)

  open ProvingGuide.Connectives.Existential using (fst; snd; _,_) public

  ∧-comm : {A B : Set} → A ∧ B → B ∧ A
  ∧-comm A∧B = (snd A∧B , fst A∧B )

  ∧-assoc : {A B C : Set} → (A ∧ B) ∧ C → A ∧ (B ∧ C)
  ∧-assoc (p , q) = (fst p , (snd p , q))

  curry : {A B C : Set} → (A ∧ B → C) → (A → (B → C))
  curry A∧B pA pB = A∧B ((pA , pB))

  uncurry : {A B C : Set} → (A → (B → C)) → (A ∧ B → C)
  uncurry p q = p (fst q) (snd q)

  ∧-map : {A A' B B' : Set} → (A → A') → (B → B') → A ∧ B → A' ∧ B'
  ∧-map mapA mapB AB = (mapA (fst AB)) , (mapB (snd AB))

  ∧-diag : {A : Set} → A → A ∧ A
  ∧-diag pA = pA , pA

  ∧-not : {A : Set} → A ∧ ⊥ → ⊥
  ∧-not p = snd p

  frobenius : {A B : Set} {P : A → Set} → ∃[ x ] (P x ∧ B) → (∃[ x ] P x) ∧ B
  frobenius (x , p) = (x , (fst p)) , snd p

  -- Leyes de De Morgan

  de-morgan₁ : {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
  de-morgan₁ (notA , notB) (left x) = notA x
  de-morgan₁ (notA , notB) (right x) = notB x

  de-morgan₂ : {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
  de-morgan₂ notAorB = (λ x → notAorB (left x)) , λ x → notAorB (right x)

  de-morgan₃ : {A B : Set} → ¬ A ∨ ¬ B → ¬ (A ∧ B)
  de-morgan₃ (left notA) AandB = notA (fst AandB)
  de-morgan₃ (right notB) AandB = notB (snd AandB)

  -- Zero Sum
  sum-zero : (a b : ℕ) → a + b ≡ 0 → a ≡ 0 ∧ b ≡ 0
  sum-zero zero zero sumZero = refl , refl
