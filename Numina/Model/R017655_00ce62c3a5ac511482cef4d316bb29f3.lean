import Mathlib

theorem number_theory_6899 (x : ℤ) (h : x^5 = 1419857) : x = 17 := by
  have h1 : x ≤ 20 := by
    by_contra h1
    push_neg at h1
    have h2 : x ≥ 21 := by
      omega
    have h3 : x ^ 5 ≥ 21 ^ 5 := by
      apply pow_le_pow_left
      all_goals nlinarith
    have h4 : (21 : ℤ) ^ 5 > (1419857 : ℤ) := by norm_num
    nlinarith
  have h2 : x ≥ 10 := by
    by_contra h2
    push_neg at h2
    have h9 : x ≤ 9 := by omega
    have h10 : x ^ 5 ≤ (59049 : ℤ) := by
      have h9 : x ≤ 9 := h9
      have h11 : x ≤ 9 := h9
      have h12 : x ≥ -20 := by
        nlinarith [sq_nonneg (x + 20 : ℤ), sq_nonneg (x * (x) : ℤ)]
      by_cases h13 : x ≥ 0
      · -- Assume x ≥ 0
        have h14 : x ≤ 9 := by omega
        have h15 : x ^ 5 ≤ (9: ℤ) ^ 5 := by
          apply pow_le_pow_left
          all_goals nlinarith
        nlinarith
      · -- Assume x < 0
        have h14 : x < (0 : ℤ) := by nlinarith
        have h15 : x ≤ -1 := by nlinarith
        have h16 : x ^ 5 ≤ (0 : ℤ) := by
          have h17 : x ≤ -1 := h15
          have h18 : x ^ 5 ≤ (0 : ℤ) := by
            have h17 : x ≤ -1 := h17
            have h21 : x + 1 ≤ 0 := by linarith
            have h22 : x ^ 5 = x * x * x * x * x := by ring
            rw [h22]
            nlinarith [sq_nonneg (x ^ 2 : ℤ), sq_nonneg (x + 1 : ℤ), sq_nonneg (x), sq_nonneg ((x + 1) * x), sq_nonneg (x * (x ^ 2)), sq_nonneg ((x + 1) * (x ^ 2)), sq_pos_of_pos (show (2 : ℤ) > 0 by norm_num)]
          linarith
        nlinarith
    nlinarith
  interval_cases x <;> norm_num at h <;> omega