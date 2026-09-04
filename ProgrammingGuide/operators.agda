module ProgrammingGuide.operators where
open import ProgrammingGuide.boolean

and_p : Bool → Bool → Bool
and_p false false = false
and_p false true = false
and_p true false = false
and_p true true = true

-- Se puede hacer también como infijo

infixr 6 _and_ -- 6 es el nivel de prioridad de las operaciones, cuanto más alto sea, más prioridad tendrá para asociar.
_and_ : Bool → Bool → Bool
true and true = true
_ and _ = false

infixr 5 _or_
_or_ : Bool → Bool → Bool
true or _ = true
_ or y = y
