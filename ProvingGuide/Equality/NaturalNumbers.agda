module ProvingGuide.Equality.NaturalNumbers where

  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Equality.General
  open import ProgrammingGuide.Natural.Base
  open import ProgrammingGuide.Natural.Arit
  open import ProvingGuide.EvenOdd
  open import ProvingGuide.Equality.Reasoning.Core

  add-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
  add-assoc zero b c = refl
  add-assoc (succ a) b c = cong succ (add-assoc a b c)

  add-zero : (a : ℕ) → (a + 0) ≡ a
  add-zero zero = refl
  add-zero (succ a) = cong succ (add-zero a)

  add-succ : (a b : ℕ) → succ a + b ≡ a + succ b
  add-succ zero b = refl
  add-succ (succ a) b = cong succ (add-succ a b)

  add-comm : (a b : ℕ) → a + b ≡ b + a
  add-comm zero b = sym (add-zero b)
  add-comm (succ a) b = trans (cong succ (add-comm a b)) (add-succ b a)

  add-one : (a : ℕ) → a + 1 ≡ succ a
  add-one zero = refl
  add-one (succ a) = cong succ (add-one a)

  zero-+-zero-eq-zero : (a b : ℕ) → a ≡ 0 → b ≡ 0 → a + b ≡ 0
  zero-+-zero-eq-zero a b refl refl = refl

  left-add : (a b c : ℕ) → a ≡ b → c + a  ≡ c + b
  left-add a b c refl = refl

  right-add : (a b c : ℕ) → a ≡ b → a + c ≡ b + c
  right-add a b c refl = refl

  two-+-+ : (a : ℕ) → a + a ≡ 2 · a
  two-+-+ a = refl

  mul-zero : (a : ℕ) → a · 0 ≡ 0
  mul-zero zero = refl
  mul-zero (succ a) = trans (add-zero (a · 0)) (mul-zero a)

  mul-one : (a : ℕ) → a · 1 ≡ a
  mul-one zero = refl
  mul-one (succ a) = trans (trans (add-comm (a · 1) 1) refl) (cong succ (mul-one a))

  mul-succ : (a b : ℕ) → a · succ b ≡ a + a · b
  mul-succ zero b = refl
  mul-succ (succ a) b = trans (trans (cong (λ t → t + succ b) (mul-succ a b)) (trans (add-assoc a (a · b) (succ b)) (left-add (a · b + succ b) (succ (succ a · b)) a (trans (trans (left-add (succ b) (b + 1) (a · b) (sym (add-one b))) (trans (sym (add-assoc (a · b) b 1)) refl)) (add-one (succ a · b))) )) ) (sym (add-succ a (succ a · b)))

  mul-comm : (a b : ℕ) → a · b ≡ b · a
  mul-comm zero b = sym (mul-zero b)
  mul-comm (succ a) b = trans (add-comm (a · b) b) (trans (left-add (a · b) (b · a) b (mul-comm a b)) (sym (mul-succ b a)))

  add-dist-mul : (a b c : ℕ) → (a + b) · c ≡ a · c + b · c
  add-dist-mul zero b c = refl
  add-dist-mul (succ a) b c = trans (trans (trans (cong (_+ c) (add-dist-mul a b c)) (add-assoc (a · c) (b · c) c)) (left-add (b · c + c) (c + b · c) (a · c) (add-comm (b · c) c))) (sym (add-assoc (a · c) c (b · c)))

  succ-injective : {n m : ℕ} → succ n ≡ succ m → n ≡ m
  succ-injective {n} {m} refl = refl

  twice-even : (a : ℕ) → Even (twice a)
  twice-even zero = base-even
  twice-even (succ a) = step-even (twice-even a)

  add-comm' : (a b : ℕ) → a + b ≡ b + a
  add-comm' zero b = sym (add-zero b)
  add-comm' (succ a) b = begin
    succ a + b ≡⟨⟩
    succ (a + b) ≡⟨ cong succ (add-comm' a b) ⟩
    succ (b + a) ≡⟨  add-succ b a ⟩
    b + succ a ∎

  mul-dist-add : (a b c : ℕ) → a · (b + c) ≡ a · b + a · c
  mul-dist-add a b c = begin
    a · (b + c) ≡⟨ mul-comm a (b + c) ⟩
    (b + c) · a ≡⟨ add-dist-mul b c a ⟩
    b · a + c · a ≡⟨ cong₂ _+_ (mul-comm b a) (mul-comm c a) ⟩
    a · b + a · c ∎

  binomial-theorem : (a b : ℕ) → (a + b) ² ≡ a ² + 2 · (a · b) + b ²
  binomial-theorem a b = begin
    (a + b) ² ≡⟨ add-dist-mul a b (a + b) ⟩
    a · (a + b) + b · (a + b) ≡⟨ cong₂ _+_ (mul-dist-add a a b) (mul-dist-add b a b) ⟩
    a · a + a · b + (b · a + b · b) ≡⟨ add-assoc (a ²) (a · b) (b · a + b · b) ⟩
    a ² + (a · b + (b · a + b ²)) ≡⟨ cong (a ² +_) (cong (a · b +_) (cong (_+ b ²) (mul-comm b a))) ⟩
    a ² + (a · b + (a · b + b ²)) ≡⟨ cong (a ² +_) (sym (add-assoc (a · b) (a · b) (b ²))) ⟩
    a ² + (a · b + a · b + b ²) ≡⟨ cong (λ x → a ² + (x + b ²)) refl ⟩
    a ² + (2 · (a · b) + b ²) ≡⟨ sym (add-assoc (a ²) (a · b + a · b) (b ²)) ⟩
    a ² + 2 · (a · b) + b ² ∎
