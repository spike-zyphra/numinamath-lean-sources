import Mathlib

open Real Set
open scoped Real

theorem algebra_599344 (α : ℝ) :
  cos α + cos (120 * π / 180 - α) + cos (120 * π / 180 + α) = 0 ∧
  sin α - sin (120 * π / 180 - α) + sin (120 * π / 180 + α) = 0 := by 
  have h1 : cos α + cos (120 * π / 180 - α) + cos (120 * π / 180 + α) = 0 := by
    have hcos1 : cos (120 * π / 180 - α) = cos (120 * π / 180) * cos α + sin (120 * π / 180) * sin α := by 
      rw [cos_sub]
    have hcos2 : cos (120 * π / 180 + α) = cos (120 * π / 180) * cos α - sin (120 * π / 180) * sin α := by 
      rw [cos_add]
    have hcos120 : cos (120 * π / 180) = -1 / 2 := by 
      have h1 : 120 * π / 180 = π - π / 3 := by ring_nf
      rw [h1]
      rw [cos_pi_sub]
      norm_num
    have hsin120 : sin (120 * π / 180) = Real.sqrt 3 / 2 := by 
      have h1 : 120 * π / 180 = π - π / 3 := by ring_nf
      rw [h1]
      rw [sin_pi_sub]
      have h2 : sin (π / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
      rw [h2]
    rw [hcos1, hcos2, hcos120, hsin120]
    ring_nf
  have h2 : sin α - sin (120 * π / 180 - α) + sin (120 * π / 180 + α) = 0 := by 
    have hsin1 : sin (120 * π / 180 - α) = sin (120 * π / 180) * cos α - cos (120 * π / 180) * sin α := by 
      rw [sin_sub]
    have hsin2 : sin (120 * π / 180 + α) = sin (120 * π / 180) * cos α + cos (120 * π / 180) * sin α := by 
      rw [sin_add]
    have hcos120 : cos (120 * π / 180) = -1 / 2 := by 
      have h1 : 120 * π / 180 = π - π / 3 := by ring_nf
      rw [h1]
      rw [cos_pi_sub]
      norm_num
    have hsin120 : sin (120 * π / 180) = Real.sqrt 3 / 2 := by 
      have h1 : 120 * π / 180 = π - π / 3 := by ring_nf
      rw [h1]
      rw [sin_pi_sub]
      have h2 : sin (π / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
      rw [h2]
    rw [hsin1, hsin2, hcos120, hsin120]
    ring_nf
  exact ⟨h1, h2⟩