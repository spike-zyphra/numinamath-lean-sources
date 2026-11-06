import Mathlib

theorem algebra_19722 : 0.8 + (∑' n : ℕ, 0.04 * 0.1 ^ n) -
    ∑' n : ℕ, 0.4 * 0.1 ^ n = (2 / 5 : ℝ) := by
  have h1 : (∑' n : ℕ, (0.04 * (0.1 : ℝ) ^ n)) = (2 / 45 : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  have h2 : (∑' n : ℕ, (0.4 * (0.1 : ℝ) ^ n)) = (4 / 9 : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1, h2]
  all_goals norm_num