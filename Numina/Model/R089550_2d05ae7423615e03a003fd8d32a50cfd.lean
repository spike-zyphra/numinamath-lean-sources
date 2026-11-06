import Mathlib

open Real
open scoped BigOperators

theorem algebra_121679 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![2, 1, -1]) (hB : B = ![6, -1, -4]) (hC : C = ![4, 2, 1]) :
  let v1 := B - A
  let v2 := C - A
  let cosθ := (inner v1 v2) / (norm v1 * norm v2)
  cosθ = 0 := by
  rw [hA, hB, hC]
  simp [Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  <;> norm_num
  <;> ring_nf
  <;> norm_num