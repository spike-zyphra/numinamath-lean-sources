import Mathlib

theorem number_theory_15581 : (∑' n : ℕ, 0.1 * 0.1 ^ n) + (∑' n : ℕ, 0.02 * 0.01 ^ n) +
    (∑' n : ℕ, 0.003 * 0.001 ^ n) = (164 / 1221 : ℝ) := by

  have h1 : (∑' n : ℕ, 0.1 * 0.1 ^ n) = (1 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num

  have h2 : (∑' n : ℕ, 0.02 * 0.01 ^ n) = (2 / 99 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num

  have h3 : (∑' n : ℕ, 0.003 * 0.001 ^ n) = (1 / 333 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num

  rw [h1, h2, h3]
  norm_num