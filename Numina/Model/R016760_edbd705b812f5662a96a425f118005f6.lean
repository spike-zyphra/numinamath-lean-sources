import Mathlib

theorem inequalities_183239 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 4 * a * b * c = a + b + c + 1) :
    a ^ 2 + a + b ^ 2 + b + c ^ 2 + c ≥ 2 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - 2 * a * b), sq_nonneg (a + b + c - 2 * b * c), sq_nonneg (a + b + c - 2 * c * a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]