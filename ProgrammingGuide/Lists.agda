module ProgrammingGuide.Lists where

  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit

  infixr 5 _∷_
  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  sum : List ℕ → ℕ
  sum [] = 0
  sum (n ∷ nList) = n + (sum nList)

  length : {A : Set} → List A → ℕ -- Los corchetes son para que Agda pueda inferir el tipo de la lista.
  length [] = 0
  length (n ∷ X) = succ (length X)

  replicate : {A : Set} → ℕ → A → List A
  replicate 0 x = []
  replicate (succ n) x = x ∷ (replicate n x)

  infixr 5 _++_
  _++_ : {A : Set} → List A → List A → List A
  [] ++ Y = Y
  (x ∷ X) ++ Y = x ∷ (X ++ Y)

  flat : {A : Set} → List (List A) → List A
  flat [] = []
  flat (x ∷ s) = x ++ (flat s)

  drop : {A : Set} (k : ℕ) → List A → List A
  drop 0 xs = xs
  drop _ [] = []
  drop (succ n) (x ∷ xs) = drop n xs

  map : {A B : Set} → (A → B) → List A → List B
  map _ [] = []
  map f (x ∷ xs) = (f x) ∷ (map f xs)

  _!!_ : {A : Set} → List A → A → List A
  xs !! z = xs ++ (z ∷ [])

  reverse : {A : Set} → List A → List A
  reverse [] = []
  reverse (x ∷ xs) = (reverse xs) !! x

  downFrom : ℕ → List ℕ
  downFrom 0 = []
  downFrom (succ n) = n ∷ (downFrom n)

  upTo : ℕ → List ℕ
  upTo 0 = []
  upTo (succ n) = (upTo n) !! n
