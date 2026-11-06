import Mathlib

theorem algebra_9129 {s : ℝ → ℝ} (hs : s = fun t => t ^ 2 + 3 / t) :
    deriv s 2 = 13 / 4 := by 
  rw [hs]
  simp [deriv_add, deriv_pow, deriv_div, deriv_const, deriv_id', div_eq_mul_inv,
      mul_comm]
  all_goals
    norm_num [deriv_pow, deriv_div, deriv_const, differentiableAt_id', differentiableAt_inv]
    all_goals
      norm_num