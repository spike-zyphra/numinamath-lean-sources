import Mathlib

theorem algebra_12020 : ∑' n : ℕ, 0.43 * 0.01 ^ n = (43 / 99 : ℝ) := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one]
  all_goals norm_num
  all_goals norm_num