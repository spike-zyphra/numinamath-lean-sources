import Mathlib

theorem algebra_312092 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + a * b + b^2 / 3 = 25) (h2 : b^2 / 3 + c^2 = 9)
    (h3 : a^2 + a * b * a^2 + a * c + c^2 = 16) :
    a * b + 2 * b * c + 3 * a * c = 24 * Real.sqrt 3 := by
  have h4 : (a * b + 2 * b * c + 3 * a * c) ^ 2 = (24 * Real.sqrt 3) ^ 2 := by
    nlinarith [sq_nonneg (a - b * (1 / 2)), sq_nonneg (b - c * Real.sqrt 3), sq_nonneg (a - c * (Real.sqrt 3 / 2)), Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sqrt_nonneg 3, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h5 : a * b + 2 * b * c + 3 * a * c ≥ 0 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h6 : (24 * Real.sqrt 3) ≥ 0 := by
    positivity
  nlinarith [h4, h5, h6, Real.sqrt_nonneg 3]