import Mathlib

theorem inequalities_598861 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    3 ≤ a^2 + b^2 + c^2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]