import Mathlib

open Real
open scoped BigOperators

theorem algebra_129428 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![0, -3, 6]) (hB : B = ![-12, -3, -3]) (hC : C = ![-9, -3, -6]) :
  let v1 := B - A
  let v2 := C - A
  cos (arccos (inner v1 v2 / (norm v1 * norm v2))) = 0.96 := by
  rw [hA] at *
  rw [hB] at *
  rw [hC] at *
  simp [EuclideanSpace.norm_eq, inner, Fin.sum_univ_three, Fin.isValue, sub_eq_zero]
  norm_num [cos_arccos]