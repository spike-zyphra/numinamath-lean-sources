import Mathlib

theorem algebra_13635 : (∑' n : ℕ, 0.09 * 0.01 ^ n) * (∑' n : ℕ, 0.7 * 0.1 ^ n) = (7 / 99 : ℝ) := by
  have h1 : ∑' n : ℕ, 0.09 * 0.01 ^ n = (1 / 11 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  have h2 : ∑' n : ℕ, 0.7 * 0.1 ^ n = (7 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1, h2]
  all_goals norm_num