import Mathlib

open Real Set
open scoped Real

theorem algebra_101237 :
  (cos (75 * π / 180) ^ 4 + sin (75 * π / 180) ^ 4 +
    3 * sin (75 * π / 180) ^ 2 * cos (75 * π / 180) ^ 2) /
  (cos (75 * π / 180) ^ 6 + sin (75 * π / 180) ^ 6 +
    4 * sin (75 * π / 180) ^ 2 * cos (75 * π / 180) ^ 2) = 1 := by

  have h1 : cos (75 * π / 180)^2 + sin (75 * π / 180)^2 = 1 := by
    exact Real.cos_sq_add_sin_sq (75 * π / 180)

  have numerator_eq : cos (75 * π / 180) ^ 4 + sin (75 * π / 180) ^ 4 + 3 * sin (75 * π / 180) ^ 2 * cos (75 * π / 180) ^ 2 = 1 + (cos (75 * π / 180) * sin (75 * π / 180))^2 := by
    have h4 : cos (75 * π / 180) ^ 4 + sin (75 * π / 180) ^ 4 = (cos (75 * π / 180) ^ 2 + sin (75 * π / 180) ^ 2)^2 - 2 * (cos (75 * π / 180) * sin (75 * π / 180))^2 := by
      ring_nf
    rw [h4, h1]
    ring

  have denominator_eq : cos (75 * π / 180) ^ 6 + sin (75 * π / 180) ^ 6 + 4 * sin (75 * π / 180) ^ 2 * cos (75 * π / 180) ^ 2 = 1 + (cos (75 * π / 180) * sin (75 * π / 180))^2 := by
    have h5 : cos (75 * π / 180) ^ 6 + sin (75 * π / 180) ^ 6 = (cos (75 * π / 180) ^ 2 + sin (75 * π / 180) ^ 2)^3 - 3 * (cos (75 * π / 180) ^ 2 * sin (75 * π / 180) ^ 2) * (cos (75 * π / 180) ^ 2 + sin (75 * π / 180) ^ 2) := by
      ring_nf
    rw [h5, h1]
    ring

  rw [numerator_eq, denominator_eq]
  field_simp
  <;> nlinarith [Real.sin_sq_add_cos_sq (75 * π / 180)]