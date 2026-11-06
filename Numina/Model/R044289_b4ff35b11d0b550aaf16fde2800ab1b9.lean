import Mathlib

open Real

theorem calculus_23353 : 1 / (2 * sin (10 * π / 180)) - 2 * sin (70 * π / 180) = 1 := by
  have h1 : sin (70 * π / 180) = cos (20 * π / 180) := by
    have h2 : 70 * π / 180 = π / 2 - 20 * π / 180 := by
      nlinarith [pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  rw [h1]
  have h2_pos : sin (10 * π / 180) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 10 * π / 180
      nlinarith [pi_pos]
    · -- Show 10 * π / 180 < π
      nlinarith [pi_pos]
  have h2_ne : sin (10 * π / 180) ≠ 0 := by
    linarith [h2_pos]
  have h3 : 2 * sin (10 * π / 180) * cos (20 * π / 180) = sin (30 * π / 180) - sin (10 * π / 180) := by
    have h4 : 2 * sin (10 * π / 180) * cos (20 * π / 180) = sin ((10 * π / 180) + (20 * π / 180)) + sin ((10 * π / 180) - (20 * π / 180)) := by
      rw [sin_add, sin_sub]
      ring
    rw [h4]
    have h5 : (10 * π / 180) + (20 * π / 180) = 30 * π / 180 := by 
      nlinarith [pi_pos]
    have h6 : (10 * π / 180) - (20 * π / 180) = -(10 * π / 180) := by 
      nlinarith [pi_pos]
    rw [h5, h6]
    have h7 : sin (-(10 * π / 180)) = - sin (10 * π / 180) := by
      rw [sin_neg]
    rw [h7]
    all_goals ring_nf <;> nlinarith [Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (20 * π / 180), h2_pos ]
  have h6 : sin (30 * π / 180) = 1 / 2 := by
    have h7 : 30 * π / 180 = π / 6 := by
      nlinarith [pi_pos]
    rw [h7]
    exact sin_pi_div_six
  field_simp [h2_ne]
  <;> 
    nlinarith [sq_pos_of_pos h2_pos, Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (20 * π / 180), h6, h3, Real.sin_le_one (10 * π / 180), Real.sin_le_one (20 * π / 180), Real.sin_le_one (30 * π / 180), Real.sin_sq_add_cos_sq (30 * π / 180), Real.sin_sq_add_cos_sq (60 * π / 180), Real.sin_le_one (60 * π / 180), Real.cos_le_one (10 * π / 180), Real.cos_le_one (20 * π / 180), Real.cos_le_one (60 * π / 180), Real.sin_pi_div_six, Real.sin_pi_div_three, Real.cos_pi_div_three, Real.cos_pi_div_six, Real.sin_le_one (10 * π / 180 + 20 * π / 180), Real.sin_add (10 * π / 180) (20 * π / 180)]
  all_goals linarith
  <;> 
    nlinarith [sq_pos_of_pos h2_pos, Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (20 * π / 180), h6, h3]
  all_goals linarith