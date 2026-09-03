module ProgrammingGuide.DependentFunctions where

  -- En funciones polimórficas, le pasas el "tipo" como un primer parametro y haces que el resto de parámetros dependan de él

  id : (X : Set) → X → X
  id X a = a

  -- Ejercicio, implementar una función K que lea como entrada dos tipos X e Y y dos valores x ∈ X e y ∈ Y y devuelva x.

  K : (X : Set) → (Y : Set) → (x : X) → (y : Y) → X
  K X Y x y = x
