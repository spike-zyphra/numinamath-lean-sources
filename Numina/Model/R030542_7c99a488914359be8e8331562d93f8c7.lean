import Mathlib

open Polynomial

theorem algebra_21271 {f g : Polynomial ℝ} (hf : f = X ^ 3 - 6 * X ^ 2 + 3 * X - 4)
    (hg : g = X ^ 3 + 5 * X ^ 2 + 9 * X - 2) :
    (f.comp g).coeff 0 = -42 := by
  rw [hf, hg]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, pow_two, pow_succ, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_comm]
  all_goals
    norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]