import Mathlib

open Real Set
open scoped Real

theorem algebra_185283 (α : Real) :
  2 * sin (3 * π - 2 * α) ^ 2 * cos (5 * π + 2 * α) ^ 2 =
  1 / 4 - 1 / 4 * sin ((5 / 2) * π - 8 * α) := by
  have h1 : sin (3 * π - 2 * α) = sin (2 * α) := by
    have h1 : 3 * π - 2 * α = π - 2 * α + 2 * π := by ring_nf
    rw [h1]
    have h2 : sin (π - 2 * α + 2 * π) = sin (π - 2 * α) := by
      have h3 : π - 2 * α + 2 * π = (π - 2 * α) + 2 * π := by ring_nf
      rw [h3]
      rw [sin_add_two_pi]
    rw [h2]
    have h3 : sin (π - 2 * α) = sin (2 * α) := by
      rw [sin_pi_sub]
      <;> ring_nf
    rw [h3]
  have h2 : cos (5 * π + 2 * α) = - cos (2 * α) := by
    have h1 : 5 * π + 2 * α = 2 * π + (2 * π + (π + 2 * α)) := by ring_nf
    rw [h1]
    have h2 : cos (2 * π + (2 * π + (π + 2 * α))) = cos (π + 2 * α) := by
      have h4 : 2 * π + (2 * π + (π + 2 * α)) = (π + 2 * α) + 4 * π := by ring_nf
      rw [h4]
      have h5 : cos ((π + 2 * α) + 4 * π) = cos (π + 2 * α) := by
        have h6 : cos ((π + 2 * α) + 4 * π) = cos ((π + 2 * α) + 2 * π + 2 * π) := by ring_nf
        rw [h6]
        have h7 : cos ((π + 2 * α) + 2 * π + 2 * π) = cos ((π + 2 * α) + 2 * π) := by
          rw [cos_add_two_pi]
        rw [h7]
        have h8 : cos ((π + 2 * α) + 2 * π) = cos (π + 2 * α) := by
          rw [cos_add_two_pi]
        rw [h8]
      rw [h5]
    rw [h2]
    have h3 : cos (π + 2 * α) = - cos (2 * α) := by
      rw [cos_add]
      rw [cos_pi, sin_pi]
      ring_nf
    rw [h3]
  rw [h1, h2]
  have h3 : sin ((5 / 2) * π - 8 * α) = cos (8 * α) := by
    have h1 : sin ((5 / 2) * π - 8 * α) = sin ((π / 2 - 8 * α) + 2 * π) := by
      ring_nf
    rw [h1]
    have h2 : sin ((π / 2 - 8 * α) + 2 * π) = sin (π / 2 - 8 * α) := by
      rw [sin_add_two_pi]
    rw [h2]
    have h3 : sin (π / 2 - 8 * α) = cos (8 * α) := by
      rw [sin_pi_div_two_sub]
    rw [h3]
  rw [h3]
  have h4 : 2 * sin (2 * α) ^ 2 * (-cos (2 * α)) ^ 2 =
    2 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2 := by
    ring_nf
  rw [h4]
  have h5 : 2 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2 =
    (1 / 4) * (1 - cos (8 * α)) := by
    have h1 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
      rw [show 4 * α = 2 * (2 * α) by ring_nf]
      rw [sin_two_mul]
      <;> ring_nf
    have h2 : sin (8 * α) = 2 * sin (4 * α) * cos (4 * α) := by
      rw [show 8 * α = 2 * (4 * α) by ring_nf]
      rw [sin_two_mul]
      <;> ring_nf
    have h3 : cos (8 * α) = 1 - 2 * sin (4 * α) ^ 2 := by
      have h4 : cos (8 * α) = cos (2 * (4 * α)) := by ring_nf
      rw [h4]
      rw [cos_two_mul]
      rw [sin_sq]
      <;> ring_nf
    have h4 : sin (4 * α) ^ 2 = 4 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2 := by
      rw [h1]
      ring_nf
    nlinarith [Real.sin_sq_add_cos_sq (4 * α), Real.sin_sq_add_cos_sq (2 * α), Real.sin_sq_add_cos_sq (8 * α)]
  nlinarith [Real.sin_sq_add_cos_sq (2 * α), Real.sin_sq_add_cos_sq (4 * α), Real.sin_sq_add_cos_sq (8 * α)]