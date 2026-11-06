import Mathlib

open Real Set
open scoped Real

theorem algebra_280644 : sin (45 * π / 180) = sin (75 * π / 180) - sin (15 * π / 180) := by
  have h1 : sin (45 * π / 180) = sin (π / 4) := by
    ring_nf
  have h2 : sin (75 * π / 180) = sin (5 * π / 12) := by
    ring_nf
  have h3 : sin (15 * π / 180) = sin (π / 12) := by
    ring_nf
  rw [h1, h2, h3]
  have h4 : sin (5 * π / 12) = sin (π / 4 + π / 6) := by
    ring_nf
  have h5 : sin (π / 12) = sin (π / 4 - π / 6) := by
    ring_nf
  rw [h4, h5]
  rw [sin_add, sin_sub]
  have h6 : sin (π / 4) = Real.sqrt 2 / 2 := by
    rw [sin_pi_div_four]
  have h7 : cos (π / 4) = Real.sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  have h8 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  have h9 : cos (π / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  rw [h6, h7, h8, h9]
  ring_nf
  <;> field_simp
  <;> ring_nf <;> field_simp
  all_goals linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]