import Mathlib

theorem inequalities_598378 (a b c : ℝ) : a^2 + b^2 + c^2 - (a * b + b * c + c * a) ≥ 3 * (b - c) * (a - b) := by
  suffices ((a + c) - 2 * b) ^ 2 ≥ 0 by
    linarith
  apply sq_nonneg