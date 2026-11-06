import Mathlib

open Real Set
open scoped Real

theorem algebra_185986 (α : ℝ) :
  1 + cos (2 * α + 270 * π / 180) + sin (2 * α + 450 * π / 180) =
  2 * sqrt 2 * cos α * cos (45 * π / 180 - α) := by

  have h1 : cos (2 * α + 270 * π / 180) = sin (2 * α) := by
    have h2 : 2 * α + 270 * π / 180 = 2 * α - π / 2 + 2 * π := by 
      ring_nf
    rw [h2]
    have h3 : cos (2 * α - π / 2 + 2 * π) = cos (2 * α - π / 2) := by
      rw [show 2 * α - π / 2 + 2 * π = (2 * α - π / 2) + 2 * π by ring]
      rw [cos_add_two_pi]
    rw [h3]
    have h4 : cos (2 * α - π / 2) = sin (2 * α) := by 
      rw [cos_sub]
      simp [cos_pi_div_two, sin_pi_div_two]
      <;> ring
    rw [h4]

  have h2 : sin (2 * α + 450 * π / 180) = cos (2 * α) := by 
    have h3 : 2 * α + 450 * π / 180 = 2 * α + π / 2 + 2 * π := by 
      ring_nf
    rw [h3]
    have h4 : sin (2 * α + π / 2 + 2 * π) = sin (2 * α + π / 2) := by
      rw [show 2 * α + π / 2 + 2 * π = (2 * α + π / 2) + 2 * π by ring]
      rw [sin_add_two_pi]
    rw [h4]
    have h5 : sin (2 * α + π / 2) = cos (2 * α) := by 
      rw [sin_add_pi_div_two]
    rw [h5]

  rw [h1, h2]

  have h6 : 45 * π / 180 = π / 4 := by 
    ring_nf

  rw [h6]

  have h7 : cos (π / 4 - α) = (Real.sqrt 2 / 2) * (cos α + sin α) := by
    rw [cos_sub]
    have h8 : cos (π / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    have h9 : sin (π / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    rw [h8, h9]
    ring

  rw [h7]

  have h8 : 2 * Real.sqrt 2 * cos α * ((Real.sqrt 2 / 2) * (cos α + sin α)) = 2 * cos α * (cos α + sin α) := by
    ring_nf
    <;> norm_num [Real.mul_self_sqrt]
    <;> ring

  have h5 : 1 + sin (2 * α) + cos (2 * α) = 2 * cos α * (cos α + sin α) := by 
    have h6 : sin (2 * α) = 2 * sin α * cos α := by
      rw [sin_two_mul]
    have h7 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by 
      rw [cos_two_mul]
    rw [h6, h7]
    have h8 : cos α ^ 2 + sin α ^ 2 = 1 := by 
      exact Real.cos_sq_add_sin_sq α
    nlinarith [h8]

  linarith [h8, h5, Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num : (0 : ℝ) < 2)]