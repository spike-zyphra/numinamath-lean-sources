import Mathlib

open Real Set
open scoped Real

theorem algebra_162893 (x : ℝ) :
  sin (x + 2 * π) * cos (2 * x - 7 * π / 2) +
  sin (3 * π / 2 - x) * sin (2 * x - 5 * π / 2) = cos (3 * x) := by 
  have h1 : sin (x + 2 * π) = sin x := by
    rw [sin_add, sin_two_pi, cos_two_pi]
    simp
  have h2 : cos (2 * x - 7 * π / 2) = -sin (2 * x) := by 
    have h3 : 2 * x - 7 * π / 2 = (2 * x + π / 2) - 4 * π := by
      ring
    rw [h3]
    have h4 : cos ((2 * x + π / 2) - 4 * π) = cos (2 * x + π / 2) := by
      have h5 : cos ((2 * x + π / 2) - 4 * π) = cos ((2 * x + π / 2) - 2 * π - 2 * π) := by
        ring_nf
      rw [h5]
      have h6 : cos ((2 * x + π / 2) - 2 * π - 2 * π) = cos ((2 * x + π / 2) - 2 * π) := by 
        rw [show (2 * x + π / 2) - 2 * π - 2 * π = ((2 * x + π / 2) - 2 * π) - 2 * π by ring]
        rw [cos_sub_two_pi]
      have h7 : cos ((2 * x + π / 2) - 2 * π) = cos (2 * x + π / 2) := by 
        rw [cos_sub_two_pi]
      rw [h6, h7]
    rw [h4]
    have h8 : cos (2 * x + π / 2) = -sin (2 * x) := by
      rw [cos_add]
      simp [cos_pi_div_two, sin_pi_div_two]
    linarith [h8]
  have h3 : sin (3 * π / 2 - x) = -cos x := by 
    have h9 : sin (3 * π / 2 - x) = sin (3 * π / 2) * cos x - cos (3 * π / 2) * sin x := by
      rw [sin_sub]
      all_goals ring_nf
    have h10 : sin (3 * π / 2) = -1 := by
      have h11 : sin (3 * π / 2) = sin (π + π / 2) := by 
        ring_nf
      rw [h11]
      rw [sin_add]
      simp [sin_pi, cos_pi, sin_pi_div_two, cos_pi_div_two]
    have h11 : cos (3 * π / 2) = 0 := by 
      have h12 : cos (3 * π / 2) = cos (π + π / 2) := by 
        ring_nf
      rw [h12]
      rw [cos_add]
      simp [cos_pi, sin_pi, cos_pi_div_two, sin_pi_div_two]
    rw [h9, h10, h11]
    all_goals ring_nf
  have h4 : sin (2 * x - 5 * π / 2) = -cos (2 * x) := by
    have h12 : 2 * x - 5 * π / 2 = (2 * x + 3 * π / 2) - 4 * π := by
      ring
    rw [h12]
    have h13 : sin ((2 * x + 3 * π / 2) - 4 * π) = sin (2 * x + 3 * π / 2) := by 
      have h14 : sin ((2 * x + 3 * π / 2) - 4 * π) = sin ((2 * x + 3 * π / 2) - 2 * π - 2 * π) := by 
        ring_nf
      rw [h14]
      have h15 : sin ((2 * x + 3 * π / 2) - 2 * π - 2 * π) = sin ((2 * x + 3 * π / 2) - 2 * π) := by 
        rw [show (2 * x + 3 * π / 2) - 2 * π - 2 * π = ((2 * x + 3 * π / 2) - 2 * π) - 2 * π by ring]
        rw [sin_sub_two_pi]
      have h16 : sin ((2 * x + 3 * π / 2) - 2 * π) = sin (2 * x + 3 * π / 2) := by 
        rw [sin_sub_two_pi]
      rw [h15, h16]
    rw [h13]
    have h17 : sin (2 * x + 3 * π / 2) = -cos (2 * x) := by
      have h18 : sin (2 * x + 3 * π / 2) = sin (2 * x + π + π / 2) := by
        ring_nf
      rw [h18]
      have h19 : sin (2 * x + π + π / 2) = - sin (2 * x + π / 2) := by
        rw [show 2 * x + π + π / 2 = (2 * x + π / 2) + π by ring]
        rw [sin_add_pi]
      have h20 : sin (2 * x + π / 2) = cos (2 * x) := by 
        rw [sin_add]
        simp [cos_pi_div_two, sin_pi_div_two]
      rw [h19, h20]
    linarith [h17]
  rw [h1, h2, h3, h4]
  have h5 : cos (3 * x) = cos (2 * x) * cos x - sin (2 * x) * sin x := by
    have h7 : cos (3 * x) = cos (2 * x + x)  := by 
      ring_nf
    rw [h7]
    rw [cos_add]
    <;> ring_nf
  rw [h5]
  have h8 : sin (2 * x) = 2 * sin x * cos x := by 
    rw [sin_two_mul]
  have h9 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
    rw [cos_two_mul]
  simp [h8, h9]
  <;> nlinarith [Real.cos_sq_add_sin_sq x, sq_nonneg (cos x - 1), sq_nonneg (sin x)]