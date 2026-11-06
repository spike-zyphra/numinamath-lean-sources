import Mathlib

theorem inequalities_109257 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) : a + b + c ≥ a * b * c + 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
           sq_nonneg (a + b + c - 3), sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
           mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]