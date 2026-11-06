import Mathlib

theorem algebra_9237 (s : ℝ → ℝ) (h₀ : s = fun t => t^2 + 3 / t) :
    deriv s 2 = 13 / 4 := by
  rw [h₀]
  simp [deriv_add, deriv_pow, deriv_div, deriv_const, deriv_id', div_eq_mul_inv, differentiableAt_id', differentiableAt_inv]
  all_goals norm_num [deriv_pow, deriv_div, deriv_const, differentiableAt_id', differentiableAt_inv, differentiableAt_pow]