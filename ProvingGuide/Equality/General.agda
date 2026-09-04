module ProvingGuide.Equality.General where

  open import ProvingGuide.Equality.Base
  open import ProvingGuide.Negation

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym {A} {x} {y} refl = refl

  cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {A} {x} {y} {z} refl refl = refl

  ext : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
  ext refl = refl

  subst : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
  subst F refl Fx = Fx

  infix 4 _≢_
  _≢_ : {X : Set} → X → X → Set
  a ≢ b = ¬ (a ≡ b)

  ≢-symm : {X : Set} {a b : X} → a ≢ b → b ≢ a
  ≢-symm p refl = p refl

  infix 4 _≗_
  _≗_ : {A B : Set} → (A → B) → (A → B) → Set
  f ≗ g = (x : _) → f x ≡ g x
