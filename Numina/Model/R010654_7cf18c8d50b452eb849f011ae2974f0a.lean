import Mathlib

theorem algebra_15451 : (∑' n : ℕ, 0.6 * 0.1 ^ n) * 6 = (4 : ℝ) := by
  have h1 : (∑' n : ℕ, 0.6 * 0.1 ^ n) = (2 / 3 : ℝ) := by 
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  norm_num