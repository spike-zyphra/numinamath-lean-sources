import Mathlib

theorem inequalities_601801 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (8 * a + 5 * b + 5 * c)^3 + (5 * a + 8 * b + 5 * c)^3 +
    (5 * a + 5 * b + 8 * c)^3 ≥
    1944 * (a + b + c) * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]