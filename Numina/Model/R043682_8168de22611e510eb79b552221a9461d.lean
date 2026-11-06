import Mathlib

theorem algebra_292410 : ∀ x : ℝ, x^12 - x^7 - x^5 + 1 ≥ 0 := by
  intro x
  by_cases h : x ≥ 1
  .
    have k1 : x ^ 12 - x ^ 7 - x ^ 5 + 1 = (x ^ 5 - 1) * (x ^ 7 - 1) := by
      ring
    rw [k1]
    have k2 : (x ^ 5 - 1) ≥ 0 := by
      have k3 : x ^ 5 ≥ 1 := by
        have k4 : x ≥ 1 := h
        have k5 : x ^ 5 ≥ (1 : ℝ) ^ 5 := by
          apply pow_le_pow_left
          all_goals nlinarith
        have k6 : (1 : ℝ) ^ 5 = 1 := by
          norm_num
        nlinarith [k5, k6]
      linarith
    have k3 : (x ^ 7 - 1) ≥ 0 := by
      have k4 : x ^ 7 ≥ 1 := by
        have k5 : x ≥ 1 := h
        have k6 : x ^ 7 ≥ (1 : ℝ) ^ 7 := by
          apply pow_le_pow_left
          all_goals nlinarith
        have k7 : (1 : ℝ) ^ 7 = 1 := by
          norm_num
        nlinarith [k6, k7]
      linarith
    nlinarith
  .
    have h2 : x < 1 := by linarith
    have h3 : x ^ 12 - x ^ 7 - x ^ 5 + 1 = (x ^ 5 - 1) * (x ^ 7 - 1) := by
      ring
    rw [h3]
    have h4 : (x ^ 5 - 1) * (x ^ 7 - 1) ≥ 0 := by
      by_cases h5 : x ≥ 0
      · -- Then 0 ≤ x < 1. Both factors are ≤ 0.
        have h6 : x < 1 := h2
        have h5'1 : x ^ 5 ≤ 1 := by
          have h7 : x ≤ (1 : ℝ) := by linarith
          have h8 : x ^ 5 ≤ (1 : ℝ) ^ 5 := by
            apply pow_le_pow_left
            all_goals nlinarith
          have h9 : (1 : ℝ) ^ 5 = 1 := by
            norm_num
          have h10 : x ^ 5 ≤ (1 : ℝ) := by
            linarith [h8, h9]
          linarith
        have h5'2 : x ^ 7 ≤ 1 := by
          have h7 : x ≤ (1 : ℝ) := by linarith
          have h8 : x ^ 7 ≤ (1 : ℝ) ^ 7 := by
            apply pow_le_pow_left
            all_goals nlinarith
          have h9 : (1 : ℝ) ^ 7 = 1 := by
            norm_num
          have h10 : x ^ 7 ≤ (1 : ℝ) := by
            linarith [h8, h9]
          linarith
        have h7'1 : x ^ 5 - 1 ≤ 0 := by linarith
        have h7'2 : x ^ 7 - 1 ≤ 0 := by linarith
        nlinarith
      · -- Then x < 0. The product is of two negative terms, hence ≥ 0.
        have h8 : x < 0 := by nlinarith
        have h6'1 : x ^ 5 < 0 := by
          have h9 : x < 0 := h8
          have h10 : x ^ 5 < 0 := by
            have h11 : x < 0 := h8
            have h12 : x ^ 5 = x * (x^4) := by ring
            have h13 : x ^ 4 > 0 := by
              nlinarith [sq_pos_of_neg h8]
            have h14 : x * (x^4) < 0 := by
              apply mul_neg_of_neg_of_pos
              · linarith
              · linarith
            nlinarith [h12, h14]
          linarith
        have h6'2 : x ^ 5 - 1 < 0 := by
          nlinarith
        have h6'3 : x ^ 7 < 0 := by
          have h9 : x < 0 := h8
          have h10 : x ^ 7 < 0 := by
            have h11 : x < 0 := h8
            have h12 : x ^ 7 = x * (x ^ 6) := by ring
            have h13 : x ^ 6 > 0 := by
              nlinarith [sq_pos_of_neg h8]
            have h14 : x * (x ^ 6) < 0 := by
              apply mul_neg_of_neg_of_pos
              · linarith
              · linarith
            nlinarith [h12, h14]
          linarith
        have h6'4 : x ^ 7 - 1 < 0 := by
          nlinarith
        have h6'5 : (x ^ 5 - 1) * (x ^ 7 - 1) ≥ 0 := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos (show x ^ 5 - 1 ≤ 0 by nlinarith) (show x ^ 7 - 1 ≤ 0 by nlinarith)]
        linarith
    linarith