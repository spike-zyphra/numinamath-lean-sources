import Mathlib

theorem number_theory_22791 : 3 + ∑' n, 283 * (0.001 : ℝ)^(n+1) = 3280 / 999 := by

  have h1 : ∑' n, 283 * (0.001 : ℝ)^(n + 1) = (283 / 999 : ℝ) := by

    have h2 : ∀ n : ℕ, 283 * (0.001 : ℝ) ^ (n + 1) = (283 / 1000) * (0.001 : ℝ) ^ n := by
      intro n
      ring_nf

    rw [tsum_congr h2]

    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]

    all_goals norm_num
  rw [h1]
  all_goals norm_num