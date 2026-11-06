import Mathlib

open Real

theorem algebra_10705 : ∑' n : ℕ, (3 / 2 : ℝ) * (-4 / 9 : ℝ) ^ n = 27 / 26 := by
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  all_goals norm_num