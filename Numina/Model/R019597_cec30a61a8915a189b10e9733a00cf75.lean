import Mathlib

theorem algebra_261697 {a : ℕ → ℝ} (h : ∀ n, (2 - a (n + 1)) * (4 + a n) = 8) (ha : a 0 = 2) :
    ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 2 := by

  have ha1 : ∀ (n : ℕ), a n = 2 / (2 ^ (n + 1) - 1) := by
    intro n 
    induction n with 
    | zero =>
      rw [ha]
      norm_num 
    | succ n ih =>
      have h1 := h n 
      rw [show a n = 2 / (2 ^ (n + 1) - 1) by simpa using ih] at h1
      field_simp [(show (2 : ℝ) ^ (n + 1) - 1 ≠ 0 by
        have h11 : (2 : ℝ) ^ (n + 1) ≥ (2 : ℝ) := by 
          have h111 : n + 1 ≥ 1 := by linarith 
          have h1111 : (2 : ℝ) ^ (n + 1) ≥ (2 : ℝ) ^ 1 := by 
            apply pow_le_pow_right 
            all_goals linarith 
          rw [show (2 : ℝ) ^ 1 = (2 : ℝ) by norm_num] at h1111 
          linarith 
        linarith 
      )] at h1 
      field_simp [(show (2 : ℝ) ^ (n + 1 + 1) - 1 ≠ 0 by 
        have h11 : (2 : ℝ) ^ (n + 1 + 1) ≥ (4 : ℝ) := by 
          have h111 : n + 1 + 1 ≥ 2 := by linarith 
          have h1111 : (2 : ℝ) ^ (n + 1 + 1) ≥ (2 : ℝ) ^ 2 := by 
            apply pow_le_pow_right 
            all_goals linarith 
          rw [show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num] at h1111 
          linarith 
        linarith 
      )] at *
      ring_nf at h1 ⊢ 
      <;> nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (n + 1), pow_pos (show (0 : ℝ) < 2 by norm_num) (n + 2), sq_nonneg ((2 : ℝ) ^ (n + 1) - 1), sq_nonneg (a (n + 1) - 1)]

  have h1 : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 2 := by
    intro n
    induction n with 
    | zero =>
      norm_num [Finset.sum_range_succ, ha, ha1]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : a (n + 1) = 2 / (2 ^ (n + 1 + 1) - 1) := by
        specialize ha1 (n + 1)
        simpa using ha1 
      rw [h2] 
      field_simp [(show (2 : ℝ) ^ (n + 1 + 1) - 1 ≠ 0 by 
        have h11 : (2 : ℝ) ^ (n + 1 + 1) ≥ (4 : ℝ) := by 
          have h111 : n + 1 + 1 ≥ 2 := by linarith 
          have h1111 : (2 : ℝ) ^ (n + 1 + 1) ≥ (2 : ℝ) ^ 2 := by 
            apply pow_le_pow_right 
            all_goals linarith 
          rw [show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num] at h1111 
          linarith 
        linarith 
      )] 
      ring_nf 
      <;> norm_num 
      <;> ring 
  specialize h1 n
  simpa using h1