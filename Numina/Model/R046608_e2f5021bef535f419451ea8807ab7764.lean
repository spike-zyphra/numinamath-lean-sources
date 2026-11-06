import Mathlib

open Real Set
open scoped Real

theorem algebra_186110 (α : Real) :
  sin (2*α) + sin (4*α) - sin (6*α) =
  4 * sin (3*α) * sin (2*α) * sin α := by 
  have h1 : sin (2 * α) + sin (4 * α) = 2 * sin (3 * α) * cos α := by
    have h2 : sin (2 * α) + sin (4 * α) = 2 * sin ((2 * α + 4 * α) / 2) * cos ((4 * α - (2 * α)) / 2) := by
      rw [show 2 * α = ( (2 * α + 4 * α)/2 ) - ( (4 * α - (2 * α))/2 ) by ring]
      rw [show 4 * α = ( (2 * α + 4 * α)/2 ) + ( (4 * α - (2 * α))/2 ) by ring]
      rw [sin_sub, sin_add]
      ring
    have h3 : (2 * α + 4 * α) / 2 = 3 * α := by ring
    have h4 : (4 * α - (2 * α)) / 2 = α := by ring
    rw [h3, h4] at h2
    linarith
  have h6 : sin (6 * α) = 2 * sin (3 * α) * cos (3 * α) := by
    have h2 : sin (6 * α) = sin (2 * (3 * α)) := by ring_nf
    rw [h2]
    rw [sin_two_mul]
  have h7 : cos α - cos (3 * α) = 2 * sin (2 * α) * sin α := by
    have h9 : cos α - cos (3 * α) = -2 * sin ((3 * α + α) / 2) * sin ((α - 3 * α) / 2) := by
      rw [show cos α - cos (3 * α) = -2 * sin ((3 * α + α) / 2) * sin ((α - 3 * α) / 2) by 
          rw [cos_sub_cos]
          <;> ring_nf
      ]
    have h10 : (3 * α + α) / 2 = 2 * α := by ring_nf
    have h11 : (α - 3 * α) / 2 = -α := by ring_nf
    rw [h10, h11] at h9
    have h10_neg : sin (-α) = - sin α := by
      rw [show -α = -α by rfl]
      simp [sin_neg]
    rw [h10_neg] at h9
    have h14 : sin (2 * α) = 2 * sin α * cos α := by
      rw [show 2 * α = 2 * α by rfl]
      rw [sin_two_mul]
      <;> ring
    nlinarith 
  calc
    sin (2 * α) + sin (4 * α) - sin (6 * α)
      = (sin (2 * α) + sin (4 * α)) - sin (6 * α) := by ring
    _ = (2 * sin (3 * α) * cos α) - sin (6 * α) := by rw [h1]
    _ = (2 * sin (3 * α) * cos α) - (2 * sin (3 * α) * cos (3 * α)) := by rw [h6]
    _ = 2 * sin (3 * α) * (cos α - cos (3 * α)) := by ring
    _ = 2 * sin (3 * α) * (2 * sin (2 * α) * sin α) := by rw [h7]
    _ = 4 * sin (3 * α) * sin (2 * α) * sin α := by ring