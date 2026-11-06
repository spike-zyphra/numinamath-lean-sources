import Mathlib

theorem inequalities_66654 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + 9 ≥ 4 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]