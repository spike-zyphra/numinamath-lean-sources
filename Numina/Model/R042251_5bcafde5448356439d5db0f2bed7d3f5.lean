import Mathlib

theorem inequalities_52700 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 = c^3) :
    a^2 + b^2 - c^2 > 6 * (c - a) * (c - b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          pow_two_nonneg (a - b), pow_two_nonneg (a - c), pow_two_nonneg (b - c),
          sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]