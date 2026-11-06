import Mathlib

open Real Set
open scoped Real

theorem inequalities_232080 (α : Real) :
  (cos α)^6 + (sin α)^6 ≥ 1/4 := by
  have h1 : cos α ^ 2 + sin α ^ 2 = 1 := by
    exact cos_sq_add_sin_sq α

  have h2 : (cos α)^6 + (sin α)^6 = 1 - 3 * ((cos α)^2 * (sin α)^2) := by
    have h3 : (cos α)^6 + (sin α)^6 = ((cos α)^2 + (sin α)^2)^3 - 3 * ((cos α)^2 + (sin α)^2) * ((cos α)^2 * (sin α)^2) := by
      ring_nf
    rw [h1] at h3
    nlinarith

  have h3 : (cos α)^2 * (sin α)^2 ≤ 1 / 4 := by
    have h4 : 4 * ((cos α) ^ 2 * (sin α) ^ 2) ≤ 1 := by
      have h5 : sin (2 * α) = 2 * sin α * cos α := by
        rw [sin_two_mul]
      have h6 : (sin (2 * α)) ^ 2 = 4 * (sin α) ^ 2 * (cos α) ^ 2 := by
        rw [h5]
        ring
      have h7 : (sin (2 * α)) ^ 2 ≤ 1 := by
        have h8 : sin (2 * α) ≤ 1 := by
          apply sin_le_one
        have h9 : sin (2 * α) ≥ -1 := by
          apply neg_one_le_sin
        nlinarith [sq_nonneg (sin (2 * α))]
      nlinarith [h6, h7]
    nlinarith

  rw [h2]
  nlinarith [h3]