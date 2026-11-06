import Mathlib

theorem number_theory_11203 : ∑' n, 0.81 * (0.01 : ℝ)^n - 81 / 100 = 9 / 1100 := by
  have h2 : ∑' n : ℕ, 0.81 * (0.01 : ℝ) ^ n = (9 / 11 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h2]
  all_goals norm_num
  all_goals norm_num