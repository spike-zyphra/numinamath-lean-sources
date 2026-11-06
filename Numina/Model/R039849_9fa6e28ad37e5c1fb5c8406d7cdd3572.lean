import Mathlib

open Real Set
open scoped Real

theorem algebra_232533 {α : ℝ} :
  (1 - cos (π / 12)) * (1 + sin (75 * π / 180)) +
  cos (75 * π / 180) * cos (π / 12) / tan (π / 12) = 1 ∧
  sin (45 * π / 180 - α) - cos (30 * π / 180 + α) +
  sin (30 * π / 180)^2 - cos (45 * π / 180 + α) +
  sin (60 * π / 180 - α) + sin (60 * π / 180)^2 = 1 := by 
  constructor
  · -- Solve the first expression
    have h2 : sin (75 * π / 180) = cos (π / 12) := by 
      have h3 : 75 * π / 180 = Real.pi / 2 - (π / 12) := by 
        ring_nf
      rw [h3]
      rw [sin_pi_div_two_sub]
    have h4 : cos (75 * π / 180) = sin (π / 12) := by 
      have h3 : 75 * π / 180 = Real.pi / 2 - (π / 12) := by 
        ring_nf
      rw [h3]
      rw [cos_pi_div_two_sub]
    have h5 : tan (π / 12) = sin (π / 12) / cos (π / 12) := by 
      rw [tan_eq_sin_div_cos]
    rw [h2, h4, h5]
    have h6 : cos (π / 12) ≠ 0 := by 
      have h7 : cos (π / 12) > 0 := by 
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith [show π / 12 > 0 by linarith [Real.pi_pos]]
        · linarith [show π / 12 < π by linarith [Real.pi_pos]]
      linarith
    have h7 : sin (π / 12) ≠ 0 := by 
      have h8 : sin (π / 12) > 0 := by 
        apply sin_pos_of_pos_of_lt_pi
        · linarith [show π / 12 > 0 by linarith [Real.pi_pos]]
        · linarith [show π / 12 < π by linarith [Real.pi_pos]]
      linarith
    field_simp [h6, h7]
    <;> nlinarith [Real.sin_sq_add_cos_sq (π / 12)]
  · -- Solve the second expression
    have h11 : sin (45 * π / 180 - α) = sin (45 * π / 180) * cos α - cos (45 * π / 180) * sin α := by 
      rw [sin_sub]
    have h12 : cos (30 * π / 180 + α) = cos (30 * π / 180) * cos α - sin (30 * π / 180) * sin α := by 
      rw [cos_add]
    have h13 : cos (45 * π / 180 + α) = cos (45 * π / 180) * cos α - sin (45 * π / 180) * sin α := by 
      rw [cos_add]
    have h14 : sin (60 * π / 180 - α) = sin (60 * π / 180) * cos α - cos (60 * π / 180) * sin α := by 
      rw [sin_sub]
    have h15 : sin (45 * π / 180) = Real.sqrt 2 / 2 := by
      have h16 : 45 * π / 180 = π / 4 := by 
        ring_nf
      rw [h16]
      rw [sin_pi_div_four]
    have h16 : cos (45 * π / 180) = Real.sqrt 2 / 2 := by
      have h17 : 45 * π / 180 = π / 4 := by 
        ring_nf
      rw [h17]
      rw [cos_pi_div_four]
    have h17 : sin (30 * π / 180) = 1 / 2 := by 
      have h18 : 30 * π / 180 = π / 6 := by 
        ring_nf
      rw [h18]
      rw [sin_pi_div_six]
    have h18 : cos (30 * π / 180) = Real.sqrt 3 / 2 := by 
      have h19 : 30 * π / 180 = π / 6 := by 
        ring_nf
      rw [h19]
      rw [cos_pi_div_six]
    have h19 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
      have h20 : 60 * π / 180 = π / 3 := by 
        ring_nf
      rw [h20]
      rw [sin_pi_div_three]
    have h20 : cos (60 * π / 180) = 1 / 2 := by 
      have h21 : 60 * π / 180 = π / 3 := by 
        ring_nf
      rw [h21]
      rw [cos_pi_div_three]
    rw [h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]