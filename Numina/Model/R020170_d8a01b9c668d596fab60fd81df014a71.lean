import Mathlib


theorem inequalities_235962 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a - 1) +
    (b ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * b - 1) +
    (c ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * c - 1) ≤ 3 := by

  have h1 : a + b + c = 3 := h

  have h2 : 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a - 1 > 0 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h3 : 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * b - 1 > 0 := by
    nlinarith [sq_nonneg (a - c), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h4 : 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * c - 1 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h5 : (a ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a - 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1]

  have h6 : (b ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * b - 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - c), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1]

  have h7 : (c ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * c - 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1]

  linarith [h5, h6, h7]