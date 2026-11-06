import Mathlib

theorem algebra_20747 : 1 + ∑' i : ℕ, 0.234 * 0.001 ^ i = (137 / 111 : ℝ) := by
  have h1 : ∑' i : ℕ, (0.234 : ℝ) * (0.001 : ℝ) ^ i = (26 / 111 : ℝ) := by 
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  norm_num