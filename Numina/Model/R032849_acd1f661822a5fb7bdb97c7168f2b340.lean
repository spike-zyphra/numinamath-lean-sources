import Mathlib

open Polynomial

theorem algebra_16066 {p : Polynomial ℤ} (hp : p = X ^ 4 - 3 * X + 2) :
    (p ^ 3).coeff 3 = -27 := by 
  rw [hp]
  ring_nf
  <;> norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]