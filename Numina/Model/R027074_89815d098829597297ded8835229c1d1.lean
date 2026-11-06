import Mathlib

open Polynomial

theorem algebra_3030 (p : Polynomial ℝ) (hp : p = (5 * X - 1) * (3 * X^3 - X^2 + 2)) :
    p.coeff 3 = -8 := by
  rw [hp]
  ring_nf
  <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, mul_assoc]
  <;> norm_num