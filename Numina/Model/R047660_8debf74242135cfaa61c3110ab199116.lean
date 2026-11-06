import Mathlib

theorem inequalities_162861 (a b c d : ℝ) :
    a^2 + b^2 + c^2 + d^2 ≥ a * b + (3 / 2) * b * c + c * d := by
  nlinarith [sq_nonneg (a - b / 2), sq_nonneg (d - c / 2),
          sq_nonneg (b - c), sq_nonneg (a - d),
          sq_nonneg (b + c - (a + d)), sq_nonneg (a + d - (b + c)),
          sq_nonneg (b - 2 * c), sq_nonneg (2 * a - b),
          sq_nonneg (d - 2 * c), sq_nonneg (2 * d - c)]