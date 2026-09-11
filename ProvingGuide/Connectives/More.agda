module ProvingGuide.Connectives.More where

  open import ProvingGuide.Negation
  open import ProvingGuide.Connectives.Disjunction
  open import ProgrammingGuide.HigherOrder
  open import ProgrammingGuide.Lists
  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.General
  open import ProvingGuide.Connectives.Existential
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit

  -- A es decidible si se cumple la ley del tercer excluido

  data Dec (A : Set) : Set where
    yes : A   → Dec A
    no  : ¬ A → Dec A

  dec-≡ : {A : Set} (a b : ℕ) → Dec (a ≡ b)
  dec-≡ a b = or-elim yes no (eq? a b)

  data All {A : Set} (P : A → Set) : List A → Set where
    []  : All P []
    _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

  data Any {A : Set} (P : A → Set) : List A → Set where
    here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
    there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

  infix 4 _∈_ _∉_
  _∈_ : {A : Set} → A → List A → Set
  x ∈ xs = Any (x ≡_) xs
  _∉_ : {A : Set} → A → List A → Set
  x ∉ xs = ¬ (x ∈ xs)
