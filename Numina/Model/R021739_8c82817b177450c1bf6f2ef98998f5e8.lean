import Mathlib

open Real Set
open scoped Real

theorem algebra_198744 : cos (2 * π / 5) * cos (6 * π / 5) = -1 / 4 := by
  have h1 : cos (6 * π / 5) = -cos (π / 5) := by
    have h2 : 6 * π / 5 = π + π / 5 := by
      ring_nf
    rw [h2]
    have h3 : cos (π + π / 5) = -cos (π / 5) := by
      rw [cos_add, cos_pi, sin_pi]
      ring_nf
    exact h3

  have h2 : cos (2 * π / 5) = 2 * (cos (π / 5)) ^ 2 - 1 := by
    have h3 : 2 * π / 5 = 2 * (π / 5) := by
      ring_nf
    rw [h3]
    rw [cos_two_mul]

  have h3 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
    have h4 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [cos_pi_div_five]
    exact h4

  rw [h1, h2, h3]
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]