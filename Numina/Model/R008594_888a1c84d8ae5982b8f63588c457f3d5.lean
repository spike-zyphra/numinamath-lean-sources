import Mathlib

theorem algebra_10504 : ∑' n : ℕ, (1 / 3 : ℝ) ^ n = 3 / 2 := by
  rw [tsum_geometric_of_lt_one]
  all_goals norm_num
  all_goals linarith