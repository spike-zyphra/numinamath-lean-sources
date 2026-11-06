import Mathlib

open Real Set

theorem algebra_305960 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 / a + 1 / b = sqrt 3 / c) :
    9 ≤ (2 * a ^ 2 + b ^ 2) / c ^ 2 := by
  have h1 : c ≠ 0 := by linarith
  have h2 : a ≠ 0 := by linarith
  have h3 : b ≠ 0 := by linarith
  have h4 : 2 * b + a = (sqrt 3 * (a * b) ) / c := by
    field_simp at h ⊢
    nlinarith [h, Real.sqrt_nonneg 3]
  have h5 : 0 < 2 * a ^ 2 + b ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
  have h6 : 0 < c ^ 2 := by
    nlinarith [hc]
  have h7 : 9 * c ^ 2 ≤ 2 * a ^ 2 + b ^ 2 := by
    have h9 : c * (2 * b + a) = sqrt 3 * (a * b) := by
      have h8 : 2 * b + a = (sqrt 3 * (a * b) ) / c := h4
      field_simp at h8 ⊢
      nlinarith
    have h9' : (c * (2 * b + a)) ^ 2 = 3 * (a * b) ^ 2 := by
      calc
        (c * (2 * b + a)) ^ 2 = (sqrt 3 * (a * b)) ^ 2 := by
          rw [h9]
        _ = (sqrt 3) ^ 2 * (a * b) ^ 2 := by
          ring
        _ = 3 * (a * b) ^ 2 := by
          rw [Real.sq_sqrt]
          all_goals linarith
    nlinarith [ sq_nonneg (a - b), sq_nonneg (a - sqrt 3 * c), sq_nonneg (b - sqrt 3 * c), 
          sq_nonneg (a * b), sq_nonneg (c * (2 * b + a) - sqrt 3 * (a * b)), 
          Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
  have h8 : (2 * a ^ 2 + b ^ 2) / c ^ 2 ≥ 9 := by
    have h9 : 2 * a ^ 2 + b ^ 2 ≥ 9 * c ^ 2 := by linarith [h7]
    have h10 : 0 < c ^ 2 := h6
    have h11 : (2 * a ^ 2 + b ^ 2) / c ^ 2 ≥ (9 * c ^ 2) / c ^ 2 := by
      apply (div_le_div_right h10).mpr
      linarith
    have h12 : (9 * c ^ 2) / c ^ 2 = 9 := by
      field_simp
    linarith [h11, h12]
  linarith [h8]