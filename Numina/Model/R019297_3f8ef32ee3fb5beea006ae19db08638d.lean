import Mathlib

theorem inequalities_270485 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 * b * c + b^3 * a * c + c^3 * a * b ≤ a^5 + b^5 + c^5 := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos ha (show 0 < a * b by nlinarith), mul_pos hb (show 0 < a * b by nlinarith), mul_pos ha (show 0 < a * c by nlinarith), mul_pos hc (show 0 < a * c by nlinarith)]