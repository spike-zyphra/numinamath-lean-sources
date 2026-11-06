import Mathlib

open BigOperators

theorem algebra_13021 :
    1 + ∑' n : ℕ, 27 * 0.01 ^ (n + 1) = (14 : ℝ) / 11 := by
  have h1 : ∑' n : ℕ, 27 * (0.01 : ℝ) ^ (n + 1) = (3 / 11 : ℝ) := by
    have h2 : ∀ n : ℕ, 27 * (0.01 : ℝ) ^ (n + 1) = 27 * (0.01) * (0.01 : ℝ) ^ n := by
      intro n
      ring_nf
    rw [tsum_congr h2]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  norm_num