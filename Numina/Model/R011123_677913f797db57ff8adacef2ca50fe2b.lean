import Mathlib

theorem algebra_224104 {a r : ℝ} (hr1 : r ≥ 0) (hsum : ∑' n : ℕ, a * r ^ n = 2) (hr2 : r < 1) (ha : a ≠ 0)
    (hsumsq : ∑' n : ℕ, (a * r ^ n) ^ 2 = 6) :
    ∑' n : ℕ, (a * r ^ n) ^ 3 = 96 / (7 : ℝ) := by
  have eq1 : ∑' n : ℕ, a * r ^ n = a / (1 - r) := by
    calc 
      ∑' n : ℕ, a * r ^ n = a * (∑' n : ℕ, r ^ n) := by
        rw [tsum_mul_left]
      _ = a * (1 / (1 - r)) := by
        have h1 : ∑' n : ℕ, r ^ n = 1 / (1 - r) := by 
          rw [tsum_geometric_of_norm_lt_one]
          · norm_num 
          · -- Prove that ‖r‖ < 1
            have h2 : |r| < (1 : ℝ) := by 
              have h3 : r < (1 : ℝ) := hr2 
              have h4 : r ≥ (0 : ℝ) := hr1 
              rw [abs_of_nonneg (by linarith)]
              all_goals 
                try linarith 
            simpa using h2 
        rw [h1]
      _ = a / (1 - r) := by 
        field_simp 
  have eq2 : ∑' n : ℕ, (a * r ^ n) ^ 2 = a ^ 2 / (1 - r ^ 2) := by
    calc 
      ∑' n : ℕ, (a * r ^ n) ^ 2 = ∑' n : ℕ, a ^ 2 * (r ^ 2) ^ n := by 
        congr 
        funext n 
        ring_nf 
      _ = a ^ 2 * (∑' n : ℕ, (r ^ 2) ^ n) := by 
        rw [tsum_mul_left]
      _ = a ^ 2 * (1 / (1 - r ^ 2)) := by 
        have h1 : ∑' n : ℕ, (r ^ 2) ^ n = 1 / (1 - r ^ 2) := by 
          rw [tsum_geometric_of_norm_lt_one]
          · norm_num
          · -- Prove that ‖r ^ 2‖ < 1
            have h2 : |(r ^ 2 : ℝ)| < (1 : ℝ) := by 
              have h3 : r ≥ (0 : ℝ) := hr1 
              have h4 : r < (1 : ℝ) := hr2 
              have h5 : r ^ 2 < (1 : ℝ) := by nlinarith [sq_nonneg r, mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r by linarith)]
              have abs_r2_eq : |(r ^ 2 : ℝ)| = r ^ 2 := by 
                apply abs_of_nonneg 
                nlinarith [sq_nonneg r]
              rw [abs_r2_eq]
              all_goals 
                try linarith
            simpa using h2 
        rw [h1]
      _ = a ^ 2 / (1 - r ^ 2) := by 
        field_simp 
  have eq3 : ∑' n : ℕ, (a * r ^ n) ^ 3 = a ^ 3 / (1 - r ^ 3) := by
    calc 
      ∑' n : ℕ, (a * r ^ n) ^ 3 = ∑' n : ℕ, a ^ 3 * (r ^ 3) ^ n := by 
        congr 
        funext n 
        ring_nf 
      _ = a ^ 3 * (∑' n : ℕ, (r ^ 3) ^ n) := by 
        rw [tsum_mul_left]
      _ = a ^ 3 * (1 / (1 - r ^ 3)) := by 
        have h1 : ∑' n : ℕ, (r ^ 3) ^ n = 1 / (1 - r ^ 3) := by 
          rw [tsum_geometric_of_norm_lt_one]
          · norm_num 
          · -- Prove that ‖r ^ 3‖ < 1
            have h2 : |(r ^ 3 : ℝ)| < (1 : ℝ) := by 
              have h3 : r ≥ (0 : ℝ) := hr1 
              have h4 : r < (1 : ℝ) := hr2 
              have h5 : r ^ 3 < (1 : ℝ) := by nlinarith [sq_nonneg r, mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r by linarith)]
              have abs_r3_eq : |(r ^ 3 : ℝ)| = r ^ 3 := by 
                apply abs_of_nonneg 
                nlinarith [sq_nonneg r, mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r by linarith)]
              rw [abs_r3_eq]
              all_goals 
                try linarith
            simpa using h2 
        rw [h1]
      _ = a ^ 3 / (1 - r ^ 3) := by 
        field_simp
  rw [eq1] at hsum 
  rw [eq2] at hsumsq
  have eq4 : a = 2 * (1 - r) := by
    have h5 : 1 - r ≠ 0 := by nlinarith 
    field_simp [h5] at hsum 
    linarith 
  rw [show a ^ 2 = (2 * (1 - r)) ^ 2 by rw [eq4]] at hsumsq 
  have h5 : r = -1 / 5 := by
    have h6 : r < 1 := hr2
    have h7 : r ≥ 0 := hr1
    field_simp [(show 1 - r ≠ 0 by nlinarith), (show 1 - r ^ 2 ≠ 0 by nlinarith)] at hsumsq hsum
    nlinarith 
  nlinarith [h5, hr1]