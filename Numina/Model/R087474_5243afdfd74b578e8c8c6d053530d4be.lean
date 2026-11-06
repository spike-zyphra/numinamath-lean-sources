import Mathlib

theorem inequalities_182044 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 * b + b^3 * c + c^3 * a ≥ a * b * c * (a + b + c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]