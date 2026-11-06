import Mathlib

theorem algebra_190166 (m : ℝ) : m^3 + m^2 - m - 1 > 0 ↔ m > 1 := by
  constructor
  · -- Assume $m^3 + m^2 - m - 1 > 0$, prove $m > 1$.
    intro h
    have h1 : m ^ 3 + m ^ 2 - m - 1 = (m - 1) * (m + 1) ^ 2 := by
      ring
    rw [h1] at h
    have h2 : (m + 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h3 : m - 1 > 0 := by
      nlinarith [h, h2]
    linarith
  · -- Assume $m > 1$, prove $m^3 + m^2 - m - 1 > 0$.
    intro h
    have h1 : m ^ 3 + m ^ 2 - m - 1 = (m - 1) * (m + 1) ^ 2 := by
      ring
    rw [h1]
    have h2 : m - 1 > 0 := by linarith
    have h3 : (m + 1) ^ 2 > 0 := by
      nlinarith
    nlinarith [h2, h3]