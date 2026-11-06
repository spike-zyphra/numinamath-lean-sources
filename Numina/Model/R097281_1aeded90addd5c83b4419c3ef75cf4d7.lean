import Mathlib

theorem inequalities_140375 (a b c : ℝ) : a^2 + 4 * b^2 + 8 * c^2 ≥ 3 * a * b + 4 * b * c + 2 * c * a := by
  nlinarith [sq_nonneg (a - (3 * b + 2 * c) / 2), sq_nonneg (b - 2 * c),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]