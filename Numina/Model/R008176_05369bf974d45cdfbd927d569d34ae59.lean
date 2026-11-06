import Mathlib

theorem algebra_20867 {a : ℝ} (ha : a = ∑' n, 0.2 * (0.1 : ℝ)^n + ∑' n, 0.6 * (0.1 : ℝ)^n) : 1 / a = 1.125 := by
  have h1 : ∑' n, 0.2 * (0.1 : ℝ)^n = (2 / 9 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  have h2 : ∑' n, 0.6 * (0.1 : ℝ)^n = (2 / 3 : ℝ) := by
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  have ha2 : a = (8 / 9 : ℝ) := by
    rw [ha, h1, h2]
    norm_num
  rw [ha2]
  norm_num