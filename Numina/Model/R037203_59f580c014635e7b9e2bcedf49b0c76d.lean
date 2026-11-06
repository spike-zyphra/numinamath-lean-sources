import Mathlib

theorem inequalities_4863 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / 2 * a ^ 5 + 3 * a ^ 4 * b + 4 * a ^ 3 * b ^ 2 + 7 / 2 * a ^ 2 * b ^ 2 * c + 1 / 2 * b ^ 5 + 3 * b ^ 4 * c + 4 * b ^ 3 * c ^ 2 + 7 / 2 * b ^ 2 * c ^ 2 * a + 1 / 2 * c ^ 5 + 3 * c ^ 4 * a + 4 * c ^ 3 * a ^ 2 + 7 / 2 * c ^ 2 * a ^ 2 * b ≥ 11 * a ^ 3 * b * c + 11 * b ^ 3 * c * a + 11 * c ^ 3 * a * b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]