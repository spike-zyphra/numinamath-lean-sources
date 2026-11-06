import Mathlib

theorem algebra_190158 (a : ℝ) (ha : a^4 + a^3 - a - 1 < 0) : -1 < a ∧ a < 1 := by
  have h1 : a^4 + a^3 - a - 1 = (a^2 - 1) * (a^2 + a + 1) := by
    ring
  have h2 : a^2 + a + 1 > 0 := by
    nlinarith [sq_nonneg (a + 1 / 2)]
  rw [h1] at ha
  have h3 : a^2 - 1 < 0 := by
    nlinarith
  have h4 : a^2 < 1 := by
    linarith
  constructor
  · -- -1 < a
    nlinarith [sq_nonneg (a), h4]
  · -- a < 1
    nlinarith [sq_nonneg (a), h4]