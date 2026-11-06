import Mathlib

theorem inequalities_26177 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ 2 + b + 3 / 4) * (b ^ 2 + a + 3 / 4) ≥
    (2 * a + 1 / 2) * (2 * b + 1 / 2) := by
  nlinarith [sq_nonneg (a * b - 1 / 2), sq_nonneg (a - b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2),
      mul_pos ha hb, mul_pos ha (show 0 < a by linarith), mul_pos hb (show 0 < b by linarith)]