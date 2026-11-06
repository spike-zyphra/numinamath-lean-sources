import Mathlib

theorem algebra_15667 :
    0.4 + ∑' n, (0.5 : ℚ) * 0.1 ^ (n + 1) = 41 / 90 := by
  have h1 : ∑' n, (0.5 : ℚ) * 0.1 ^ (n + 1) = (1 / 18 : ℚ) := by
    have h2 : ∀ n : ℕ, (0.5 : ℚ) * 0.1 ^ (n + 1) = (0.5 * 0.1 : ℚ) * (0.1 : ℚ) ^ n := by
      intro n
      ring_nf
    have h3 : ∑' n, (0.5 : ℚ) * 0.1 ^ (n + 1) = ∑' n, (0.5 * 0.1 : ℚ) * (0.1 : ℚ) ^ n := by
      congr 1
      funext n
      exact h2 n
    have h4 : ∑' n, (0.5 * 0.1 : ℚ) * (0.1 : ℚ) ^ n = (0.5 * 0.1 : ℚ) * (∑' n, (0.1 : ℚ) ^ n) := by
      rw [tsum_mul_left]
    have h5 : ∑' (n : ℕ), (0.1 : ℚ) ^ n = 1 / (1 - (0.1 : ℚ)) := by 
      rw [tsum_geometric_of_norm_lt_one]
      · field_simp
      all_goals
        try { 
          norm_num [norm, abs]
        }
    have eq : ∑' n, (0.5 : ℚ) * 0.1 ^ (n + 1) = (0.5 * 0.1 : ℚ) * (1 / (1 - (0.1 : ℚ))) := by 
      rw [h3, h4, h5]
    rw [eq]
    all_goals norm_num
  rw [h1]
  norm_num