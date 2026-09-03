module ProgrammingGuide.Vectors where
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit

  infixr 5 _∷_
  data Vector (A : Set) : ℕ → Set where
    [] : Vector A 0
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
  lengthV {n} v = n

-- Repetir todo lo de listas aka coñazo
