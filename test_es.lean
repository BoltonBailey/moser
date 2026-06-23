import Mathlib
open EuclideanSpace

-- The file uses local notation ℝ² for EuclideanSpace ℝ (Fin 2)
example : EuclideanSpace ℝ (Fin 2) :=
  fun (i : Fin 2) => (0 : ℝ)
