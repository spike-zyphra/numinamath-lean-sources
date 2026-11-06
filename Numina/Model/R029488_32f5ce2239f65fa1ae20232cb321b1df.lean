import Mathlib
open Polynomial

theorem algebra_13503 {p : ℤ[X]} {hp : p = (X^2 + (C 3)*X + (C (-2)))^4} :
  p.coeff 3 = -72 := by
  rw [hp]
  ring_nf
  <;> norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]