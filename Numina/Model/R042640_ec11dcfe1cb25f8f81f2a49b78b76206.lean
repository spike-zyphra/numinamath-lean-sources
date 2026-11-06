import Mathlib

theorem inequalities_598792 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a^2 + b^2 + c^2 + 2 * Real.sqrt (3 * a * b * c) ≤ 1 := by
  have h1 : a^2 + b^2 + c^2 = (a + b + c)^2 - 2 * (a * b + b * c + c * a) := by
    ring
  rw [h] at h1
  have h2 : a^2 + b^2 + c^2 = 1 - 2 * (a * b + b * c + c * a) := by
    linarith [h1]
  have h5 : (a * b + b * c + c * a)^2 ≥ 3 * a * b * c := by 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  have h6 : Real.sqrt (3 * a * b * c) ≤ a * b + b * c + c * a := by
    have h7 : 3 * a * b * c ≤ (a * b + b * c + c * a)^2 := by
      linarith [h5]
    have h8 : Real.sqrt (3 * a * b * c) ≤ Real.sqrt ((a * b + b * c + c * a)^2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have h9 : Real.sqrt ((a * b + b * c + c * a) ^ 2) = (a * b + b * c + c * a) := by
      rw [Real.sqrt_sq (show 0 ≤ (a * b + b * c + c * a : ℝ) by nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc])]
    nlinarith [Real.sqrt_nonneg (3 * a * b * c), h8, h9, Real.sqrt_nonneg ((a * b + b * c + c * a) ^ 2)]
  nlinarith [h2, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, Real.sqrt_nonneg (3 * a * b * c), Real.sq_sqrt (show 3 * a * b * c ≥ 0 by positivity)]