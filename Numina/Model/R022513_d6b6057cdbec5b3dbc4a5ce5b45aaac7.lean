import Mathlib

theorem inequalities_3376 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : c < a + b) :
  a ^ 8 + b ^ 8 ≥ c ^ 8 / 128 := by
  have h2 : a + b > c := by linarith
  have h3 : a ^ 8 + b ^ 8 ≥ ( (a + b) ^ 8 ) / 128 := by
    nlinarith [sq_nonneg (a ^ 4 - b ^ 4), sq_nonneg (a ^ 4 + b ^ 4),
          sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a ^ 3 + b ^ 3), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b),
          sq_nonneg ((a - b) * (a ^ 2 - b ^ 2)), sq_nonneg ((a - b) * (a ^ 3 - b ^ 3)), sq_nonneg ((a ^ 2 - b ^ 2) * (a ^ 3 - b ^ 3)), mul_pos ha hb, mul_pos ha ha, mul_pos hb hb,
          pow_pos ha 2, pow_pos ha 3, pow_pos ha 4, pow_pos ha 5, pow_pos ha 6, pow_pos ha 7, pow_pos ha 8, pow_pos hb 2, pow_pos hb 3, pow_pos hb 4, pow_pos hb 5, pow_pos hb 6, pow_pos hb 7, pow_pos hb 8
        ]
  have h4 : (a + b) ^ 8 > c ^ 8 := by
    have h5 : 0 < c := hc
    have h6 : a + b > c := h2
    have h7 : 0 < a + b := by nlinarith
    have h8 : (a + b) ^ 8 > c ^ 8 := by
      apply pow_lt_pow_left
      all_goals nlinarith
    linarith
  have h5 : ( (a + b) ^ 8 ) / 128 ≥ ( c ^ 8 / 128 ) := by
    have h6 : (a + b) ^ 8 ≥ c ^ 8 := by
      linarith [h4]
    linarith
  linarith [h3, h5]