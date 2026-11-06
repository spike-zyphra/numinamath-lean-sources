import Mathlib

open Polynomial Bivariate

theorem algebra_9436 (k : ℝ) (p : ℝ[X][Y]) (hp : p = C X ^ 2 - C (C (3 * k) * X) * Y - 3 * Y ^ 2 +  C (6 * X) * Y - 8)
    (hp' : (p.coeff 1).coeff 1 = 0) : k = 2 := by
  rw [hp] at hp'
  simp [coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, mul_comm] at hp'
  linarith