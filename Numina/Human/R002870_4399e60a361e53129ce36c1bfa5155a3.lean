import Mathlib

open Real
open scoped BigOperators

theorem algebra_124100 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![0, 1, -2]) (hB : B = ![3, 1, 2]) (hC : C = ![4, 1, 1]) :
  let v1 := B - A
  let v2 := C - A
  let cosθ := (inner v1 v2) / (‖v1‖ * ‖v2‖)
  cosθ = 0.96 := by
    simp [Fin.sum_univ_three, hA, hB, hC, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_one]
    norm_num [sqrt_eq_iff_eq_sq]