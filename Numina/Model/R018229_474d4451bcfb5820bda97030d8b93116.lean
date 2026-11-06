import Mathlib

open Real Set
open scoped Real

theorem algebra_163878 (α : Real) :
  (cos ((5/4)*π - 2*α))^2 - (cos ((5/4)*π + 2*α))^2 = sin (4*α) := by
  have h1 : cos ((5 / 4) * π - 2 * α) = cos ((5 / 4) * π) * cos (2 * α) + sin ((5 / 4) * π) * sin (2 * α) := by 
    rw [cos_sub]
  have h2 : cos ((5 / 4) * π + 2 * α) = cos ((5 / 4) * π) * cos (2 * α) - sin ((5 / 4) * π) * sin (2 * α) := by 
    rw [cos_add]
  have h3 : cos ((5 / 4) * π) = -Real.sqrt 2 / 2 := by
    have h4 : cos ((5 / 4) * π) = cos (π + (Real.pi / 4)) := by 
      ring_nf
    rw [h4]
    have h5 : cos (π + (Real.pi / 4)) = -cos (Real.pi / 4) := by 
      rw [cos_add, cos_pi, sin_pi]
      ring
    rw [h5]
    have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    rw [h6]
    all_goals ring
  have h4 : sin ((5 / 4) * π) = -Real.sqrt 2 / 2 := by
    have h5 : sin ((5 / 4) * π) = sin (π + (Real.pi / 4)) := by 
      ring_nf
    rw [h5]
    have h6 : sin (π + (Real.pi / 4)) = -sin (Real.pi / 4) := by 
      rw [sin_add, cos_pi, sin_pi]
      ring
    rw [h6]
    have h7 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h7]
    all_goals ring
  rw [h1, h2, h3, h4]
  have h5 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by 
    have h6 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by 
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [sin_two_mul]
    linarith
  rw [h5]
  nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (2 * α), sq_nonneg (sin (2 * α) - cos (2 * α)), sq_nonneg (sin (2 * α) + cos (2 * α))]