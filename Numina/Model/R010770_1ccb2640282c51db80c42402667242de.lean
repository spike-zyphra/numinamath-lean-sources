import Mathlib

theorem algebra_11819 : 4 + ∑' n : ℕ, 0.054 * 0.001 ^ n = (150 / 37 : ℝ) := by 
  have h1 : ∑' n : ℕ, (0.054 : ℝ) * (0.001 : ℝ) ^ n = (2 / 37 : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  norm_num