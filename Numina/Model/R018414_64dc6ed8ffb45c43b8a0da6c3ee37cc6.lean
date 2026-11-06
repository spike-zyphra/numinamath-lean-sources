import Mathlib

open Real Set
open scoped Real

theorem inequalities_186337 : cos 2 - cos 8 < 0 := by 
  have h1 : cos 2 - cos 8 = 2 * sin 5 * sin 3 := by
    have h2 : cos 2 - cos 8 = -2 * sin ((2 + 8) / 2) * sin ((2 - 8) / 2) := by
      rw [cos_sub_cos]
      <;> ring_nf 
    have h3 : (2 + 8 : ℝ) / 2 = (5 : ℝ) := by norm_num
    have h4 : (2 - 8 : ℝ) / 2 = (-3 : ℝ) := by norm_num
    rw [h3, h4] at h2 
    have h5 : sin (-3 : ℝ) = -sin (3 : ℝ) := by 
      rw [show (-3 : ℝ) = - (3 : ℝ) by ring]
      rw [sin_neg]
    rw [h5] at h2
    linarith
  rw [h1]
  have h2 : sin (5 : ℝ) < 0 := by
    have h11 : sin (5 : ℝ) = -sin (2 * Real.pi - 5) := by
      have h15 : sin (2 * Real.pi - 5) = - sin 5 := by 
        rw [sin_sub, sin_two_pi, cos_two_pi]
        norm_num 
        <;> ring_nf 
      linarith 
    have h12 : sin (2 * Real.pi - 5) > 0 := by
      have h15 : 0 < 2 * Real.pi - 5 := by
        nlinarith [Real.pi_lt_31416, Real.pi_gt_31415]
      have h16 : 2 * Real.pi - 5 < Real.pi := by
        nlinarith [Real.pi_lt_31416, Real.pi_gt_31415]
      have h17 : sin (2 * Real.pi - 5) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith 
      linarith
    linarith 
  have h3 : sin (3 : ℝ) > 0 := by
    have h5 : 0 < (3 : ℝ) := by linarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h6 : (3 : ℝ) < Real.pi := by
      linarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h7 : sin (3 : ℝ) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith 
    linarith
  nlinarith