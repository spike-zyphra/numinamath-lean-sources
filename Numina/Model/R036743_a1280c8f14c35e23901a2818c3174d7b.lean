import Mathlib

theorem algebra_16594 : ∑' n, 3 * (0.1 : ℝ)^(n+1) + ∑' n, 2 * (0.1 : ℝ)^(n+1) = 5 / 9 := by
  have h1 : ∑' n, 3 * (0.1 : ℝ)^(n+1) = (1 / 3 : ℝ) := by
    have h2 : ∀ n : ℕ, 3 * (0.1 : ℝ)^(n+1) = 3 / 10 * (0.1 : ℝ)^n := by
      intro n
      ring_nf
    rw [tsum_congr h2]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  have h3 : ∑' n, 2 * (0.1 : ℝ)^(n+1) = (2 / 9 : ℝ) := by
    have h4 : ∀ n : ℕ, 2 * (0.1 : ℝ)^(n+1) = 2 / 10 * (0.1 : ℝ)^n := by
      intro n
      ring_nf
    rw [tsum_congr h4]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1, h3]
  all_goals norm_num