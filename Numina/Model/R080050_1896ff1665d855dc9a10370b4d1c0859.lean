import Mathlib

open Real Set
open scoped Real

theorem algebra_318002 : tan (70 * π / 180) * cos (10 * π / 180) * (sqrt 3 * tan (20 * π / 180) - 1) = -1 := by
  have htan70 : tan (70 * π / 180) = sin (70 * π / 180) / cos (70 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  have htan20 : tan (20 * π / 180) = sin (20 * π / 180) / cos (20 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  have h1 : sin (70 * π / 180) = cos (20 * π / 180) := by
    have h2 : 70 * π / 180 = π / 2 - 20 * π / 180 := by
      ring 
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h3 : cos (70 * π / 180) = sin (20 * π / 180) := by
    have h4 : 70 * π / 180 = π / 2 - 20 * π / 180 := by
      ring 
    rw [h4]
    rw [cos_pi_div_two_sub]
  have h4 : cos (20 * π / 180) ≠ 0 := by
    have h1 : 0 < (20 : ℝ) * π / 180 := by
      have h2 : 0 < π := by 
        exact pi_pos
      nlinarith [pi_pos]
    have h3 : cos (20 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith [show (20 : ℝ) * π / 180 < π / 2 by nlinarith [pi_pos, Real.pi_gt_314]]
    linarith
  have h5 : sin (20 * π / 180) ≠ 0 := by 
    have h1 : 0 < (20 : ℝ) * π / 180 := by
      have h2 : 0 < π := by 
        exact pi_pos
      nlinarith [pi_pos]
    have h3 : sin (20 * π / 180) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals nlinarith [pi_pos]
    linarith
  have h6 : cos (70 * π / 180) ≠ 0 := by
    rw [h3]
    exact h5
  have h7 : sin (70 * π / 180) ≠ 0 := by
    rw [h1]
    exact h4
  rw [htan70, htan20]
  field_simp [h6, h4, h5, h7]
  have h8 : sqrt 3 * sin (20 * π / 180) - cos (20 * π / 180) = -2 * sin (10 * π / 180) := by 
    have h9 : sqrt 3 * sin (20 * π / 180) - cos (20 * π / 180) = 2 * sin (20 * π / 180 - π / 6) := by 
      rw [sin_sub, sin_pi_div_six, cos_pi_div_six]
      ring_nf <;> field_simp [Real.sqrt_pos.mpr pi_pos] <;> ring
    have h10 : sin (20 * π / 180 - π / 6) = - sin (10 * π / 180) := by 
      have h11 : 20 * π / 180 - π / 6 = - (10 * π / 180) := by 
        nlinarith [pi_pos]
      rw [h11]
      rw [sin_neg]
    rw [h9, h10]
    ring
  rw [h8, h1, h3]
  have h14 : sin (20 * π / 180) = 2 * sin (10 * π / 180) * cos (10 * π / 180) := by
    have h15 : 20 * π / 180 = 2 * (10 * π / 180) := by 
      nlinarith [pi_pos]
    rw [h15]
    rw [sin_two_mul]
    all_goals ring
  rw [h14]
  ring_nf <;> simp [pi_pos] <;> ring_nf <;> simp [pi_pos] <;> ring