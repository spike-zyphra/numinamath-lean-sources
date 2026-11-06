import Mathlib

theorem inequalities_312752 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    32 ≤ a^4 / (b - 1)^2 + b^4 / (a - 1)^2 := by
  have hb1 : 0 < b - 1 := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have h3 : a^4 / (b - 1)^2 + b^4 / (a - 1)^2 ≥ 32 := by
    have h4 : 0 < (b - 1) ^ 2 * (a - 1) ^ 2 := by positivity
    have h6 : a^4 / (b - 1) ^ 2 + b^4 / (a - 1) ^ 2 - 32 ≥ 0 := by
      have h7 : a^4 * (a - 1) ^ 2 + b^4 * (b - 1) ^ 2 - 32 * ((b - 1) ^ 2 * (a - 1) ^ 2) ≥ 0 := by
        have h7 : a^4 ≥ 16 * (a - 1) ^ 2 := by 
          nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a - 2), sq_nonneg (a * (a - 1) - 2), sq_nonneg ((a - 1) - 1), 
            mul_pos (show 0 < a - 1 by linarith) (show 0 < a - 1 by linarith), 
            mul_pos (show 0 < a - 1 by linarith) (show 0 < a by nlinarith)]
        have h8 : b^4 ≥ 16 * (b - 1) ^ 2 := by 
          nlinarith [sq_nonneg (b ^ 2 - 4), sq_nonneg (b - 2), sq_nonneg (b * (b - 1) - 2), sq_nonneg ((b - 1) - 1), 
            mul_pos (show 0 < b - 1 by linarith) (show 0 < b - 1 by linarith), 
            mul_pos (show 0 < b - 1 by linarith) (show 0 < b by nlinarith)]
        have h9 : a^4 * (a - 1) ^ 2 + b^4 * (b - 1) ^ 2 ≥ 32 * ((b - 1) ^ 2 * (a - 1) ^ 2) := by
          nlinarith [h7, h8, sq_nonneg ((a - 1) ^ 2 - (b - 1) ^ 2), sq_nonneg ((a - 1) + (b - 1)), sq_nonneg (a - 1), sq_nonneg (b - 1), 
            mul_pos (show 0 < a - 1 by linarith) (show 0 < b - 1 by linarith), 
            mul_pos (show 0 < a - 1 by linarith) (show 0 < a by nlinarith), 
            mul_pos (show 0 < b - 1 by linarith) (show 0 < b by nlinarith)]
        linarith
      have h8 : a^4 / (b - 1) ^ 2 + b^4 / (a - 1) ^ 2 - 32 ≥ 0 := by
        have h4 : 0 < (b - 1) ^ 2 * (a - 1) ^ 2 := by positivity
        have h9' : a^4 * (a - 1) ^ 2 + b^4 * (b - 1) ^ 2 - 32 * ((b - 1) ^ 2 * (a - 1) ^ 2) ≥ 0 := h7
        have h10 : (a^4 * (a - 1) ^ 2 + b^4 * (b - 1) ^ 2 - 32 * ((b - 1) ^ 2 * (a - 1) ^ 2) ) / ((b - 1) ^ 2 * (a - 1) ^ 2) ≥ 0 := by 
          apply div_nonneg
          linarith
          positivity
        have h11 : (a^4 * (a - 1) ^ 2 + b^4 * (b - 1) ^ 2 - 32 * ((b - 1) ^ 2 * (a - 1) ^ 2) ) / ((b - 1) ^ 2 * (a - 1) ^ 2) = a^4 / (b - 1) ^ 2 + b^4 / (a - 1) ^ 2 - 32 := by 
          field_simp
          <;> ring
        linarith [h11, h10]
      linarith
    linarith
  linarith [h3]