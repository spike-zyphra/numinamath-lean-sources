import Mathlib


theorem algebra_268834 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a^3 * b^2 * c ≤ 1 / (2^4 * 3^3) := by
  have h1 : c = 1 - a - b := by linarith
  have hc1 : 0 < 1 - a - b := by nlinarith
  have h4 : a ^ 3 * b ^ 2 * c = a ^ 3 * b ^ 2 * (1 - a - b) := by
    rw [h1]
  have h5 : a ^ 3 * b ^ 2 * (1 - a - b) ≤ (1 / 2) ^ 3 * (1 / 3) ^ 2 * (1 / 6) := by 
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 6),
      sq_nonneg (a * (b - 1 / 3)), sq_nonneg (a * ((1 - a - b) - 1 / 6)),
      sq_nonneg ((b - 1 / 3) * ((1 - a - b) - 1 / 6)),
      mul_pos ha hb, mul_pos ha (show (0:ℝ) < 1 - a - b by linarith), 
      mul_pos hb (show (0:ℝ) < 1 - a - b by linarith)]
  have h6 : (1 / 2 : ℝ) ^ 3 * (1 / 3) ^ 2 * (1 / 6) = 1 / (2^4 * 3^3 : ℝ) := by norm_num
  rw [h4]
  nlinarith [h5, h6, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]