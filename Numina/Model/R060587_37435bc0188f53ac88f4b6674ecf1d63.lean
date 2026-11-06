import Mathlib

open Real

theorem algebra_163919 : (sin (24 * π / 180) * cos (6 * π / 180) - sin (6 * π / 180) * sin (66 * π / 180)) / (sin (21 * π / 180) * cos (39 * π / 180) - sin (39 * π / 180) * cos (21 * π / 180)) = -1 := by
  have h1 : sin (66 * π / 180) = cos (24 * π / 180) := by
    have h2 : 66 * π / 180 = π / 2 - 24 * π / 180 := by
      nlinarith [pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h2 : sin (24 * π / 180) * cos (6 * π / 180) - sin (6 * π / 180) * sin (66 * π / 180) = sin (18 * π / 180) := by
    rw [h1]
    have h3 : sin (24 * π / 180) * cos (6 * π / 180) - sin (6 * π / 180) * cos (24 * π / 180) = sin ( (24 * π / 180) - (6 * π / 180) ) := by 
      rw [sin_sub]
      all_goals ring_nf
      all_goals linarith [pi_pos]
    rw [h3]
    ring_nf
  have h4 : sin (21 * π / 180) * cos (39 * π / 180) - sin (39 * π / 180) * cos (21 * π / 180) = - sin (18 * π / 180) := by
    have h5 : sin (21 * π / 180) * cos (39 * π / 180) - sin (39 * π / 180) * cos (21 * π / 180) = sin ( (21 * π / 180) - (39 * π / 180) ) := by 
      rw [sin_sub]
      all_goals ring_nf
      all_goals linarith [pi_pos]
    rw [h5]
    have h6 : (21 * π / 180 : ℝ) - (39 * π / 180 : ℝ) = - (18 * π / 180 : ℝ) := by
      ring_nf
    rw [h6]
    rw [sin_neg]
    all_goals ring_nf
    all_goals linarith [pi_pos]
  have h5 : sin (18 * π / 180 : ℝ) ≠ 0 := by
    have h6 : 0 < (18 * π / 180 : ℝ) := by 
      nlinarith [pi_pos]
    have h7 : 0 < sin (18 * π / 180 : ℝ) := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals nlinarith [pi_pos]
    linarith
  rw [h2, h4]
  field_simp [h5]
  <;> nlinarith [pi_pos]