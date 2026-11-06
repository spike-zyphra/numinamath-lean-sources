import Mathlib

open Real Set
open scoped Real

theorem algebra_185530 : sqrt 3 / cos (10 * π / 180) - 1 / sin (10 * π / 180) = -4 := by
  have h1 : sin (10 * π / 180) ≠ 0 := by 
    have h1 : sin (10 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · 
        ring_nf
        linarith [Real.pi_pos]
      · 
        ring_nf
        linarith [Real.pi_pos]
    linarith
  have h2 : cos (10 * π / 180) ≠ 0 := by 
    have h2 : cos (10 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · 
        ring_nf
        linarith [Real.pi_pos]
      · 
        ring_nf
        linarith [Real.pi_pos]
    linarith
  have h3 : sqrt 3 / cos (10 * π / 180) - 1 / sin (10 * π / 180) =
      (sqrt 3 * sin (10 * π / 180) - cos (10 * π / 180)) / (cos (10 * π / 180) * sin (10 * π / 180)) := by
    field_simp [h1, h2]
    <;> ring
  have h4 : sqrt 3 * sin (10 * π / 180) - cos (10 * π / 180) = -2 * sin (20 * π / 180) := by
    have h5 : 20 * π / 180 = 2 * (10 * π / 180) := by ring
    have h7 : sqrt 3 * sin (10 * π / 180) - cos (10 * π / 180) = 
        2 * (cos (30 * π / 180) * sin (10 * π / 180) - sin (30 * π / 180) * cos (10 * π / 180)) := by
      have h80 : cos (30 * π / 180) = Real.sqrt 3 / 2 := by
        have h60 : 30 * π / 180 = π / 6 := by ring
        rw [h60]
        rw [cos_pi_div_six]
      have h81 : sin (30 * π / 180) = 1 / 2 := by
        have h60 : 30 * π / 180 = π / 6 := by ring
        rw [h60]
        rw [sin_pi_div_six]
      rw [h80, h81]
      all_goals ring
    rw [h7]
    have h8 : cos (30 * π / 180) * sin (10 * π / 180) - sin (30 * π / 180) * cos (10 * π / 180) = - sin (20 * π / 180) := by 
      have h20 : 20 * π / 180 = (30 * π / 180 - 10 * π / 180 : ℝ) := by 
        nlinarith [Real.pi_pos]
      have h14 : sin (20 * π / 180) = sin (30 * π / 180 - 10 * π / 180) := by 
        rw [show 20 * π / 180 = (30 * π / 180 - 10 * π / 180 : ℝ) by linarith]
      have h12 : sin (30 * π / 180 - 10 * π / 180) = sin (30 * π / 180) * cos (10 * π / 180) - cos (30 * π / 180) * sin (10 * π / 180) := by 
        rw [sin_sub]
      rw [h12] at h14
      have h15 : cos (30 * π / 180) * sin (10 * π / 180) - sin (30 * π / 180) * cos (10 * π / 180) = - (sin (30 * π / 180) * cos (10 * π / 180) - cos (30 * π / 180) * sin (10 * π / 180)) := by 
        ring
      rw [h15]
      rw [h14]
    linarith [h8]
  have h5 : cos (10 * π / 180) * sin (10 * π / 180) = (1 / 2) * sin (20 * π / 180) := by
    have h20 : 20 * π / 180 = 2 * (10 * π / 180) := by ring
    have h8 : sin (20 * π / 180) = 2 * sin (10 * π / 180) * cos (10 * π / 180) := by 
      rw [show 20 * π / 180 = 2 * (10 * π / 180) by ring]
      rw [sin_two_mul]
    nlinarith [h8]
  rw [h3, h4, h5]
  have h8 : sin (20 * π / 180) ≠ 0 := by
    have h1 : sin (20 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · 
        ring_nf
        linarith [Real.pi_pos]
      · 
        ring_nf
        linarith [Real.pi_pos]
    linarith
  field_simp [h8]
  all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]