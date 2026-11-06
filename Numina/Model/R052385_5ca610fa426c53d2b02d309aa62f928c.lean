import Mathlib

theorem inequalities_600623 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c), sq_nonneg (a - b - c), sq_nonneg (b - a - c), sq_nonneg (c - a - b), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]