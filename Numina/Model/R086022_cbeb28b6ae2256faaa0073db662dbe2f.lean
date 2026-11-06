import Mathlib

theorem algebra_22206 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hvol : a * b * c = 216) :
    2 * (a * b + b * c + c * a) ≥ 216 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a * b - 36), sq_nonneg (b * c - 36), sq_nonneg (c * a - 36)]