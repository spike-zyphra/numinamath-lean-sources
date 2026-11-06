import Mathlib

open Real

theorem inequalities_128994 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c + a * b + b * c + c * a + a * b * c = 7) :
    sqrt (a ^ 2 + b ^ 2 + 2) + sqrt (b ^ 2 + c ^ 2 + 2) +
    sqrt (c ^ 2 + a ^ 2 + 2) ≥ 6 := by

  have h1 : sqrt (a ^ 2 + b ^ 2 + 2) ≥ (a + b + 2) / 2 := by
    have h1 : sqrt (a ^ 2 + b ^ 2 + 2) ≥ (a + b + 2) / 2 := by
      have h2 : ((a + b + 2) / 2) ^ 2 ≤ a ^ 2 + b ^ 2 + 2 := by
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb ]
      have h3 : (a + b + 2) / 2 ≤ sqrt (a ^ 2 + b ^ 2 + 2) := by
        apply le_sqrt_of_sq_le
        linarith
      linarith
    linarith

  have h2 : sqrt (b ^ 2 + c ^ 2 + 2) ≥ (b + c + 2) / 2 := by
    have h2 : sqrt (b ^ 2 + c ^ 2 + 2) ≥ (b + c + 2) / 2 := by
      have h2 : ((b + c + 2) / 2) ^ 2 ≤ b ^ 2 + c ^ 2 + 2 := by
        nlinarith [ sq_nonneg (b - c), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos hb hc ]
      have h3 : (b + c + 2) / 2 ≤ sqrt (b ^ 2 + c ^ 2 + 2) := by
        apply le_sqrt_of_sq_le
        linarith
      linarith
    linarith

  have h3 : sqrt (c ^ 2 + a ^ 2 + 2) ≥ (c + a + 2) / 2 := by
    have h3 : sqrt (c ^ 2 + a ^ 2 + 2) ≥ (c + a + 2) / 2 := by
      have h2 : ((c + a + 2) / 2) ^ 2 ≤ c ^ 2 + a ^ 2 + 2 := by
        nlinarith [ sq_nonneg (c - a), sq_nonneg (c - 1), sq_nonneg (a - 1), mul_pos hc ha ]
      have h3 : (c + a + 2) / 2 ≤ sqrt (c ^ 2 + a ^ 2 + 2) := by
        apply le_sqrt_of_sq_le
        linarith
      linarith
    linarith

  have h4 : a + b + c + 3 ≥ 6 := by
    have h5 : a + b + c ≥ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith) ]
    linarith

  have h5 : sqrt (a ^ 2 + b ^ 2 + 2) + sqrt (b ^ 2 + c ^ 2 + 2) + sqrt (c ^ 2 + a ^ 2 + 2) ≥ a + b + c + 3 := by
    linarith [h1, h2, h3]

  linarith [h5, h4]