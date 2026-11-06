import Mathlib

theorem inequalities_110679 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^3 + b^3 + a + b ≥ 4 * a * b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
          mul_pos ha hb, sq_nonneg (a + b - 2)]