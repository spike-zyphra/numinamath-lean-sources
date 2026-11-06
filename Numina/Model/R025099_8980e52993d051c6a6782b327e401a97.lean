import Mathlib

theorem inequalities_603683 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a^2 + b^2 + c^2 + d^2 = 1) :
    a^2 * b^2 * c * d + a * b^2 * c^2 * d + a * b * c^2 * d^2 + a^2 * b * c * d^2 +
    a^2 * b * c^2 * d + a * b^2 * c * d^2 ≤ 3 / 32 := by
  nlinarith [sq_nonneg (a^2 + b^2 - c^2 - d^2), sq_nonneg (a - b), sq_nonneg (c - d),
          sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
          sq_nonneg (a * b - c * d), sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c),
          sq_nonneg (a^2 + b^2 - c^2 - d^2), sq_nonneg (a^2 + c^2 - b^2 - d^2), sq_nonneg (a^2 + d^2 - b^2 - c^2),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
          mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc)) (le_of_lt hd)]