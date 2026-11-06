import Mathlib

theorem algebra_15079 : ∑' n : ℕ, (1 / 3 : ℝ) * (1 / 2) ^ n = 2 / 3 := by 
  rw [tsum_mul_left]
  rw [tsum_geometric_of_lt_one]
  all_goals norm_num