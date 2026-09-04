module ProvingGuide.Equality.Booleans where

  open import ProgrammingGuide.boolean
  open import ProgrammingGuide.operators
  open import ProvingGuide.Negation
  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.General

  false≢true : false ≢ true
  false≢true ()

  not² : (x : Bool) → not (not x) ≡ x
  not² false = refl
  not² true = refl

  and-comm : (x y : Bool) → (x and y) ≡ (y and x)
  and-comm false false = refl
  and-comm false true = refl
  and-comm true false = refl
  and-comm true true = refl
