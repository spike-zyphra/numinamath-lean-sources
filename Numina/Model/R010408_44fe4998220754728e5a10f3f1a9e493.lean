import Mathlib

theorem algebra_14528 : 3 + ∑' n : ℕ, 0.7 * 0.1 ^ n = (34 / 9 : ℝ) := by
  have h1 : ∑' n : ℕ, 0.7 * 0.1 ^ n = (7 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  all_goals norm_num