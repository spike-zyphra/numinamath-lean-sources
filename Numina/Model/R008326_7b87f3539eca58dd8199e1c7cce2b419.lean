import Mathlib

theorem algebra_13803 : (∑' n : ℕ, 0.8 * 0.1 ^ n) + (∑' n : ℕ, 0.2 * 0.1 ^ n) = (10 / 9 : ℝ) := by
  have h1 : (∑' n : ℕ, 0.8 * 0.1 ^ n) = (8 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  have h2 : (∑' n : ℕ, 0.2 * 0.1 ^ n) = (2 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1, h2]
  norm_num