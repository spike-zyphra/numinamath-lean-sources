import Mathlib
open Polynomial

theorem algebra_3163 {P : ℝ[X]} (hP : P = (2 * X + 3)^7 * (1 + X)^3) : P.coeff 8 = 10464 := by
  rw [hP]
  ring_nf
  simp [coeff_eq_zero_of_natDegree_lt]
  <;> norm_num