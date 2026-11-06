import Mathlib

theorem inequalities_6613 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) :
    12 ≤ (a + b) * (a + b * c) + (b + c) * (b + c * a) + (c + a) * (c + a * b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]