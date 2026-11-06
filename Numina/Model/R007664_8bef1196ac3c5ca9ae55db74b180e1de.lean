import Mathlib

theorem algebra_12908 : (∑' n : ℕ, 0.1 * 0.1 ^ n) + (∑' n : ℕ, 0.01 * 0.01 ^ n) = (4 / 33 : ℝ) := by
  have h1 : ∑' n : ℕ, (0.1 : ℝ) * (0.1 : ℝ) ^ n = (1 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  have h2 : ∑' n : ℕ, (0.01 : ℝ) * (0.01 : ℝ) ^ n = (1 / 99 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1, h2]
  norm_num