import Mathlib

theorem inequalities_276871 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b * (a + b) + b * c * (b + c) + a * c * (a + c) ≥ 6 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]