import Mathlib

theorem inequalities_121489 (a b : ℝ) :
    a^2 + b^2 + 2 * (a - 1) * (b - 1) ≥ 1 := by
  have h1 : a^2 + b^2 + 2 * (a - 1) * (b - 1) = (a + b - 1) ^ 2 + 1 := by
    ring
  rw [h1]
  have h2 : (a + b - 1) ^ 2 ≥ 0 := by
    exact sq_nonneg (a + b - 1)
  linarith