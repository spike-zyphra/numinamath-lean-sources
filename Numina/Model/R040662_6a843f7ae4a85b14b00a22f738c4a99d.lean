import Mathlib

open Real

theorem calculus_17259 : tan (-3 * π / 4) = 1 := by
  have h1 : tan (-3 * π / 4) = sin (-3 * π / 4) / cos (-3 * π / 4) := by 
    rw [tan_eq_sin_div_cos]
  rw [h1]
  have h2 : sin (-3 * π / 4) = -sin (3 * π / 4) := by
    have h1 : sin (-3 * π / 4) = sin (- (3 * π / 4)) := by ring_nf
    rw [h1]
    rw [sin_neg]
    <;> ring_nf
  have h3 : cos (-3 * π / 4) = cos (3 * π / 4) := by
    have h1 : cos (-3 * π / 4) = cos (- (3 * π / 4)) := by ring_nf
    rw [h1]
    rw [cos_neg]
    <;> ring_nf
  have h4 : sin (3 * π / 4) = Real.sqrt 2 / 2 := by
    have h1 : sin (3 * π / 4) = sin (π - (π / 4)) := by 
      ring_nf
    rw [h1]
    rw [sin_pi_sub]
    have h2 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h2]
    <;> ring_nf
  have h5 : cos (3 * π / 4) = -Real.sqrt 2 / 2 := by
    have h1 : cos (3 * π / 4) = cos (π - (π / 4)) := by 
      ring_nf
    rw [h1]
    rw [cos_pi_sub]
    have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    rw [h2]
    <;> ring_nf
  rw [h2, h3, h4, h5]
  field_simp
  <;> linarith
  <;> ring_nf