import Mathlib

theorem inequalities_8433 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (16 * a^2 + 8 * b + 17) * (16 * b^2 + 8 * c + 17) *
    (16 * c^2 + 8 * a + 17) ≥
    2^12 * (a + 1) * (b + 1) * (c + 1) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a - 1/4), sq_nonneg (b - 1/4), sq_nonneg (c - 1/4),
          sq_nonneg (a * b - 1/16), sq_nonneg (b * c - 1/16), sq_nonneg (c * a - 1/16),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith),
          mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith),
          mul_pos (show 0 < c * a from by nlinarith) (show 0 < a * b from by nlinarith)]