import Mathlib

theorem inequalities_213407 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^3 + b^3 = 1) :
    a^2 + a * b + b^2 - a - b > 0 := by
  have h3 : a < 1 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
      pow_pos ha 3, pow_pos hb 3, h, mul_pos ha hb]
  have h4 : b < 1 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
      pow_pos ha 3, pow_pos hb 3, h, mul_pos ha hb]
  have h5 : a^2 + a * b + b^2 - a - b > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
      sq_nonneg (a^2 - b^2), sq_nonneg (a * b - a * a), sq_nonneg (a * b - b * b), 
      mul_pos ha hb, mul_pos ha (show 0 < 1 - a by nlinarith), 
      mul_pos hb (show 0 < 1 - b by nlinarith), 
      mul_pos (show 0 < 1 - a by nlinarith) (show 0 < 1 - b by nlinarith), 
      sq_nonneg (a + b - 1), sq_nonneg ((a^2 + b^2 - (a * b)))]
  exact h5