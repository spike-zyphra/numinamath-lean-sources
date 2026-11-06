import Mathlib

open Real Set
open scoped Real

theorem algebra_185700 (α : ℝ) :
  (cos ((3 / 8) * π - (α / 4)))^2 -
  (cos ((11 / 8) * π + (α / 4)))^2 =
  (sqrt 2 / 2) * sin (α / 2) := by 
  have h1 : cos ((3 / 8) * π - (α / 4)) ^ 2 = (1 + cos ((3 / 4) * π - α / 2)) / 2 := by
    have h2 : cos ((3 / 8) * π - (α / 4)) ^ 2 = (1 + cos (2 * ((3 / 8) * π - (α / 4))) ) / 2 := by
      rw [cos_sq]
      ring
    rw [h2]
    ring_nf

  have h2 : cos ((11 / 8) * π + (α / 4)) ^ 2 = (1 + cos ((11 / 4) * π + α / 2)) / 2 := by
    have h3 : cos ((11 / 8) * π + (α / 4)) ^ 2 = (1 + cos (2 * ((11 / 8) * π + (α / 4))) ) / 2 := by
      rw [cos_sq]
      ring
    rw [h3]
    ring_nf

  rw [h1, h2]
  have h3 : cos ((11 / 4) * π + α / 2) = cos ((3 / 4) * π + α / 2) := by
    have h4 : (11 / 4) * π + α / 2 = 2 * π + ((3 / 4) * π + α / 2) := by
      ring
    rw [h4]
    have h5 : cos (2 * π + ((3 / 4) * π + α / 2)) = cos ((3 / 4) * π + α / 2) := by
      rw [cos_add, cos_two_pi, sin_two_pi]
      all_goals ring
    exact h5

  rw [h3]
  have h4 : cos ((3 / 4) * π - α / 2) - cos ((3 / 4) * π + α / 2) = 2 * sin ((3 / 4) * π) * sin (α / 2) := by
    rw [cos_sub, cos_add]
    ring_nf 
    all_goals tauto

  have h5 : (1 + cos ((3 / 4) * π - α / 2)) / 2 - (1 + cos ((3 / 4) * π + α / 2)) / 2 = (cos ((3 / 4) * π - α / 2) - cos ((3 / 4) * π + α / 2)) / 2 := by ring
  rw [h5]
  rw [h4]
  have h9 : sin ((3 / 4) * π) = Real.sqrt 2 / 2 := by
    have h8 : sin ((3 / 4) * π) = sin ((3 * π / 4)) := by 
      ring_nf
    rw [h8]
    have h9 : sin ((3 * π / 4)) = Real.sqrt 2 / 2 := by
      have h9 : sin ((3 * π / 4)) = sin (π - (π / 4)) := by ring_nf
      rw [h9]
      rw [sin_pi_sub]
      have h10 : sin (π / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      rw [h10]
    exact h9

  rw [h9]
  all_goals ring_nf