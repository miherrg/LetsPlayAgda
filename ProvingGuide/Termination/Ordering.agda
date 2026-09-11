module ProvingGuide.Termination.Ordering where
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit
  open import ProgrammingGuide.Lists
  open import ProvingGuide.Negation
  open import ProvingGuide.Connectives.Disjunction
  open import ProvingGuide.Connectives.More
  open import ProvingGuide.Connectives.Existential
  open import ProvingGuide.Connectives.Conjunction
  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.General
  open import ProvingGuide.Equality.NaturalNumbers
  open import ProvingGuide.EvenOdd

  infix 4 _≤_ _<_ _≥_ _>_
  data _≤_ : ℕ → ℕ → Set where
    z-leq-n : {n : ℕ} → zero ≤ n
    succ-leq-succ : {n m : ℕ} → (n≤m : n ≤ m) → succ n ≤ succ m

  _<_ : ℕ → ℕ → Set
  n < m = succ n ≤ m

  _>_ : ℕ → ℕ → Set
  n > m = m < n

  _≥_ : ℕ → ℕ → Set
  n ≥ m = m ≤ n

  ≤-refl : {a : ℕ} → a ≤ a
  ≤-refl {zero} = z-leq-n
  ≤-refl {succ a} = succ-leq-succ ≤-refl

  ≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans z-leq-n b-leq-c = z-leq-n
  ≤-trans (succ-leq-succ {a} {b} a-leq-b) (succ-leq-succ {b} {c} b-leq-c) = succ-leq-succ (≤-trans a-leq-b b-leq-c)

  ≤-antisymm : {a b : ℕ} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisymm z-leq-n z-leq-n = refl
  ≤-antisymm (succ-leq-succ p) (succ-leq-succ q) = cong succ (≤-antisymm p q)

  eq-to-le : {a b : ℕ} → a ≡ b → a ≤ b
  eq-to-le refl = ≤-refl

  <-irreflexive : {a : ℕ} → a < a → ⊥
  <-irreflexive (succ-leq-succ p) = <-irreflexive p

  -- Decision procedures
  ≤-<-connex : (a b : ℕ) → a ≤ b ∨ b < a
  ≤-<-connex zero b = left z-leq-n
  ≤-<-connex (succ a) zero = right (succ-leq-succ z-leq-n)
  ≤-<-connex (succ a) (succ b) with ≤-<-connex a b
  ... | left a-leq-b = left (succ-leq-succ a-leq-b)
  ... | right b-lt-a = right (succ-leq-succ b-lt-a)

  <-cmp : (a b : ℕ) → a ≡ b ∨ a < b ∨ a > b
  <-cmp zero zero = left refl
  <-cmp zero (succ b) = right (left (succ-leq-succ z-leq-n))
  <-cmp (succ a) zero = right (right (succ-leq-succ z-leq-n))
  <-cmp (succ a) (succ b) with <-cmp a b
  ... | left a-eq-b          = left (cong succ a-eq-b)
  ... | right (left a-lt-b)  = right (left (succ-leq-succ a-lt-b))
  ... | right (right a-gt-b) = right (right (succ-leq-succ a-gt-b))

  dec-≤ : (a b : ℕ) → Dec (a ≤ b)
  dec-≤ zero b = yes z-leq-n
  dec-≤ (succ a) zero = no λ ()
  dec-≤ (succ a) (succ b) with dec-≤ a b
  ... | yes p = yes (succ-leq-succ p)
  ... | no  p = no λ {(succ-leq-succ q) → p q}

  dec-< : (a b : ℕ) → Dec (a < b)
  dec-< a b = dec-≤ (succ a) b

  succ-monotone : {a b : ℕ} → a ≤ b → succ a ≤ succ b
  succ-monotone = succ-leq-succ

  pred-monotone : {a b : ℕ} → a ≤ b → pred a ≤ pred b
  pred-monotone z-leq-n = z-leq-n
  pred-monotone (succ-leq-succ a-le-b) = a-le-b

  succ-inflationary : (a : ℕ) → a ≤ succ a
  succ-inflationary zero = z-leq-n
  succ-inflationary (succ a) = succ-leq-succ (succ-inflationary a)

  twice-inflationary : (a : ℕ) → a ≤ twice a
  twice-inflationary zero = z-leq-n
  twice-inflationary (succ a) = ≤-trans (succ-inflationary (succ a)) (succ-leq-succ (succ-leq-succ (twice-inflationary a)))

  max-inflationaryₗ : (a b : ℕ) → a ≤ max a b
  max-inflationaryₗ zero b = z-leq-n
  max-inflationaryₗ (succ a) zero = ≤-refl
  max-inflationaryₗ (succ a) (succ b) = succ-leq-succ (max-inflationaryₗ a b)

  max-inflationaryᵣ : (a b : ℕ) → b ≤ max a b
  max-inflationaryᵣ a zero = z-leq-n
  max-inflationaryᵣ zero (succ b) = ≤-refl
  max-inflationaryᵣ (succ a) (succ b) = succ-leq-succ (max-inflationaryᵣ a b)

  add-monotone : {a a' b b' : ℕ} → a ≤ b → a' ≤ b' → a + a' ≤ b + b'
  add-monotone z-leq-n z-leq-n = z-leq-n
  add-monotone z-leq-n (succ-leq-succ {a'} {b'} q) = ≤-trans (succ-leq-succ (add-monotone {!!} {!!})) {!!}
  add-monotone (succ-leq-succ p) q = succ-leq-succ (add-monotone p q)

  maximum : List ℕ → ℕ
  maximum [] = zero
  maximum (x ∷ xs) = max x (maximum xs)

  maximum-≥ : (k : ℕ) (xs : List ℕ) → k ∈ xs → k ≤ maximum xs
  maximum-≥ k (x ∷ xs) (here refl) = max-inflationaryₗ k (maximum xs)
  maximum-≥ k (x ∷ xs) (there k-in-xs) = ≤-trans (maximum-≥ k xs k-in-xs) (max-inflationaryᵣ x (maximum xs))

  Even-infinite : (x : ℕ) → ∃[ y ] (y ≥ x ∧ Even y)
  Even-infinite x = (twice x) , ((twice-inflationary x) , (twice-even x))

  ℕ-infinite : (xs : List ℕ) → ∃[ x ] x ∉ xs
  ℕ-infinite xs = (succ (sum xs)) , λ p → <-irreflexive (go p)
    where
    go : {xs : List ℕ} {y : ℕ} → y ∈ xs → y < succ (sum xs)
    go (here refl) = succ-leq-succ (≤-trans (eq-to-le (sym (add-zero _))) {!!})
    go (there p) = {!!}
