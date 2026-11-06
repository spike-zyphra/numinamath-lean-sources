import Mathlib

theorem inequalities_189942 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 * a * b * c ≤ (a + b) * (b + c) * (c + a) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]