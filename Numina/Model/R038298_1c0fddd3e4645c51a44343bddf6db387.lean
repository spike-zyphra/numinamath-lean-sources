import Mathlib

open Real Set
open scoped Real

theorem algebra_189392 (α : ℝ) :
  (sin (π/8 + α/2))^2 - (sin (π/8 - α/2))^2 = sqrt 2 / 2 * sin α := by
  have h1 : (sin (π / 8 + α / 2)) ^ 2 - (sin (π / 8 - α / 2)) ^ 2 =
    (sin (π / 8 + α / 2) - sin (π / 8 - α / 2)) * (sin (π / 8 + α / 2) + sin (π / 8 - α / 2)) := by ring
  rw [h1]
  have h2 : sin (π / 8 + α / 2) - sin (π / 8 - α / 2) =
    2 * cos (π / 8) * sin (α / 2) := by
    rw [show sin (π / 8 + α / 2) = sin (π / 8) * cos (α / 2) + cos (π / 8) * sin (α / 2) by rw [sin_add],
        show sin (π / 8 - α / 2) = sin (π / 8) * cos (α / 2) - cos (π / 8) * sin (α / 2) by rw [sin_sub]]
    ring
  have h3 : sin (π / 8 + α / 2) + sin (π / 8 - α / 2) =
    2 * sin (π / 8) * cos (α / 2) := by
    rw [show sin (π / 8 + α / 2) = sin (π / 8) * cos (α / 2) + cos (π / 8) * sin (α / 2) by rw [sin_add],
        show sin (π / 8 - α / 2) = sin (π / 8) * cos (α / 2) - cos (π / 8) * sin (α / 2) by rw [sin_sub]]
    ring
  rw [h2, h3]
  have h4 : sin (π / 8) * cos (π / 8) = Real.sqrt 2 / 4 := by
    have h5 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h6 : sin (π / 8) * cos (π / 8) = (1 / 2) * sin (2 * (π / 8)) := by
      rw [sin_two_mul]
      all_goals ring
    rw [h6]
    have h7 : 2 * (π / 8) = π / 4 := by ring
    rw [h7, h5]
    all_goals ring
  have h8 : sin (α / 2) * cos (α / 2) = (1 / 2) * sin α := by
    have h9 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
      rw [←sin_two_mul]
      ring_nf
    linarith [h9]
  have h9 : (2 * cos (π / 8) * sin (α / 2)) * (2 * sin (π / 8) * cos (α / 2)) =
    4 * (sin (π / 8) * cos (π / 8)) * (sin (α / 2) * cos (α / 2)) := by
    ring_nf
  rw [h9]
  rw [h4, h8]
  ring_nf