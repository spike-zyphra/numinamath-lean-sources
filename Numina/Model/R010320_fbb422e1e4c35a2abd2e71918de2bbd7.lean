import Mathlib

open Add

theorem algebra_9221 (s : ℝ → ℝ) (h₀ : s = fun t => 4 - 2 * t + t ^ 2) :
    deriv s 3 = 4 := by 
  rw [h₀]
  simp [deriv_add, deriv_sub, deriv_pow, deriv_mul, deriv_id'', mul_comm]
  all_goals norm_num [deriv_const, deriv_id'', mul_comm]