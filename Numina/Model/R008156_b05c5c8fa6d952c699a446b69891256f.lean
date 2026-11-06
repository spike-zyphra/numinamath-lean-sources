import Mathlib

theorem algebra_14538 : 0.3 + ∑' n : ℕ, 0.025 * 0.01 ^ n = (161 / 495 : ℝ) := by
  have h : ∑' n : ℕ, (0.025 : ℝ) * (0.01) ^ n = (0.025 / (1 - (0.01 : ℝ)) : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h]
  norm_num