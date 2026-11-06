import Mathlib

theorem algebra_22089 : 72 / 100 + 6 / 1000 * ∑' n : ℕ, (1 / 10 : ℝ) ^ n = 109 / 150 := by
  have h1 : ∑' n : ℕ, (1 / 10 : ℝ) ^ n = 10 / 9 := by
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  norm_num