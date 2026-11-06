import Mathlib

open Real Set
open scoped Real

theorem algebra_153870 (α : Real) :
  2 * sin α * cos α * (cos α ^ 2 - sin α ^ 2) = sin (4 * α) / 2 := by 
  have h1 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
    rw [show 4 * α = 2 * (2 * α) by ring]
    rw [sin_two_mul]
  have h2 : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  have h3 : cos (2 * α) = cos α ^ 2 - sin α ^ 2 := by
    rw [cos_two_mul']
  rw [h1, h2, h3]
  <;> ring_nf <;> simp [mul_add, mul_sub, mul_assoc]
  <;> ring