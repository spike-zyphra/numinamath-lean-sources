import Mathlib

theorem inequalities_46285 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b + c + a * b + b * c + c * a + a * b * c = 7) :
  6 ≤ Real.sqrt (a ^ 2 + b ^ 2 + 2) + Real.sqrt (b ^ 2 + c ^ 2 + 2) +
      Real.sqrt (c ^ 2 + a ^ 2 + 2) := by
  have h1 : Real.sqrt (a ^ 2 + b ^ 2 + 2) ≥ (a + b + 2) / 2 := by
    have h_nonneg : (a + b + 2) / 2 ≥ 0 := by
      nlinarith
    have h_sq : Real.sqrt (a ^ 2 + b ^ 2 + 2) ^ 2 ≥ ((a + b + 2) / 2) ^ 2 := by
      have h2 : Real.sqrt (a ^ 2 + b ^ 2 + 2) ^ 2 = a ^ 2 + b ^ 2 + 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      have h3 : ((a + b + 2) / 2) ^ 2 ≤ a ^ 2 + b ^ 2 + 2 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb]
      nlinarith
    have h_sqrt_nonneg : Real.sqrt (a ^ 2 + b ^ 2 + 2) ≥ 0 := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (a ^ 2 + b ^ 2 + 2 : ℝ) by nlinarith), h_nonneg, h_sq, h_sqrt_nonneg]
  have h2 : Real.sqrt (b ^ 2 + c ^ 2 + 2) ≥ (b + c + 2) / 2 := by
    have h_nonneg : (b + c + 2) / 2 ≥ 0 := by
      nlinarith
    have h_sq : Real.sqrt (b ^ 2 + c ^ 2 + 2) ^ 2 ≥ ((b + c + 2) / 2) ^ 2 := by
      have h2 : Real.sqrt (b ^ 2 + c ^ 2 + 2) ^ 2 = b ^ 2 + c ^ 2 + 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      have h3 : ((b + c + 2) / 2) ^ 2 ≤ b ^ 2 + c ^ 2 + 2 := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos hb hc]
      nlinarith
    have h_sqrt_nonneg : Real.sqrt (b ^ 2 + c ^ 2 + 2) ≥ 0 := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (b ^ 2 + c ^ 2 + 2 : ℝ) by nlinarith), h_nonneg, h_sq, h_sqrt_nonneg]
  have h3 : Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ (c + a + 2) / 2 := by
    have h_nonneg : (c + a + 2) / 2 ≥ 0 := by
      nlinarith
    have h_sq : Real.sqrt (c ^ 2 + a ^ 2 + 2) ^ 2 ≥ ((c + a + 2) / 2) ^ 2 := by
      have h2 : Real.sqrt (c ^ 2 + a ^ 2 + 2) ^ 2 = c ^ 2 + a ^ 2 + 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      have h3 : ((c + a + 2) / 2) ^ 2 ≤ c ^ 2 + a ^ 2 + 2 := by
        nlinarith [sq_nonneg (c - a), sq_nonneg (c - 1), sq_nonneg (a - 1), mul_pos hc ha]
      nlinarith
    have h_sqrt_nonneg : Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ 0 := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (c ^ 2 + a ^ 2 + 2 : ℝ) by nlinarith), h_nonneg, h_sq, h_sqrt_nonneg]
  have h4 : Real.sqrt (a ^ 2 + b ^ 2 + 2) + Real.sqrt (b ^ 2 + c ^ 2 + 2) + Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ (a + b + 2) / 2 + (b + c + 2) / 2 + (c + a + 2) / 2 := by
    linarith [h1, h2, h3]
  have h5 : (a + b + 2) / 2 + (b + c + 2) / 2 + (c + a + 2) / 2 = a + b + c + 3 := by
    ring
  have h6 : a + b + c + 3 ≥ 6 := by
    have h50 : a + b + c ≥ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h]
    nlinarith
  linarith [h4, h5, h6]