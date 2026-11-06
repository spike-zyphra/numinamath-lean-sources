import Mathlib

theorem inequalities_154517 (a b : ℝ) : a^2 + b^2 + 2 * (a - 1) * (b - 1) ≥ 1 := by
  suffices (a + b - 1) ^ 2 ≥ 0 by
    linarith [this]
  apply sq_nonneg