import Mathlib

open Real

theorem algebra_196750 : tan (5 * π / 180) * tan (20 * π / 180) + tan (5 * π / 180) * tan (65 * π / 180) + tan (20 * π / 180) * tan (65 * π / 180) = 1 := by
  have htan_def1 : tan (5 * π / 180) = sin (5 * π / 180) / cos (5 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  have htan_def2 : tan (20 * π / 180) = sin (20 * π / 180) / cos (20 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  have htan_def3 : tan (65 * π / 180) = sin (65 * π / 180) / cos (65 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  rw [htan_def1, htan_def2, htan_def3]
  have h0 : sin (65 * π / 180) = cos (25 * π / 180) := by
    have h1 : 65 * π / 180 = π / 2 - 25 * π / 180 := by
      nlinarith [pi_pos]
    rw [h1]
    rw [sin_pi_div_two_sub]
  have h1 : cos (65 * π / 180) = sin (25 * π / 180) := by
    have h1 : 65 * π / 180 = π / 2 - 25 * π / 180 := by
      nlinarith [pi_pos]
    rw [h1]
    rw [cos_pi_div_two_sub]
  have h2 : sin (25 * π / 180) = sin (5 * π / 180 + 20 * π / 180) := by 
    ring_nf
  have h3 : sin (5 * π / 180 + 20 * π / 180) = sin (5 * π / 180) * cos (20 * π / 180) + cos (5 * π / 180) * sin (20 * π / 180) := by
    rw [sin_add]
  have h4 : cos (25 * π / 180) = cos (5 * π / 180 + 20 * π / 180) := by
    ring_nf
  have h5 : cos (5 * π / 180 + 20 * π / 180) = cos (5 * π / 180) * cos (20 * π / 180) - sin (5 * π / 180) * sin (20 * π / 180) := by
    rw [cos_add]
  rw [show sin (65 * π / 180) = cos (25 * π / 180) by linarith [h0]] 
  rw [show cos (65 * π / 180) = sin (25 * π / 180) by linarith [h1]]
  have h6 : sin (25 * π / 180) = sin (5 * π / 180) * cos (20 * π / 180) + cos (5 * π / 180) * sin (20 * π / 180) := by
    linarith [h2, h3]
  have h7 : cos (25 * π / 180) = cos (5 * π / 180) * cos (20 * π / 180) - sin (5 * π / 180) * sin (20 * π / 180) := by 
    linarith [h4, h5]
  rw [h6, h7]
  have h_pos1 : 0 < sin (5 * π / 180) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 5 * π / 180
      nlinarith [pi_pos]
    · -- Show 5 * π / 180 < π
      nlinarith [pi_pos]
  have h_pos2 : 0 < sin (20 * π / 180) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 20 * π / 180
      nlinarith [pi_pos]
    · -- Show 20 * π / 180 < π
      nlinarith [pi_pos]
  have h_pos3 : 0 < sin (5 * π / 180 + 20 * π / 180) := by
    have h0 : 0 < sin (5 * π / 180 + 20 * π / 180) := by 
      apply Real.sin_pos_of_pos_of_lt_pi
      · -- Show 0 < 5 * π / 180 + 20 * π / 180
        nlinarith [pi_pos]
      · -- Show 5 * π / 180 + 20 * π / 180 < π
        nlinarith [pi_pos]
    linarith
  have h_pos4 : 0 < cos (5 * π / 180) := by 
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · -- Show -(π / 2) < 5 * π / 180
      nlinarith [pi_pos]
    · -- Show 5 * π / 180 < π / 2
      nlinarith [pi_pos]
  have h_pos5 : 0 < cos (20 * π / 180) := by 
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · -- Show -(π / 2) < 20 * π / 180
      nlinarith [pi_pos]
    · -- Show 20 * π / 180 < π / 2
      nlinarith [pi_pos]
  have h_pos6 : 0 < sin (25 * π / 180) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 25 * π / 180
      nlinarith [pi_pos]
    · -- Show 25 * π / 180 < π
      nlinarith [pi_pos]
  have h_pos7 : 0 < cos (25 * π / 180) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · -- Show -(π / 2) < 25 * π / 180
      nlinarith [pi_pos]
    · -- Show 25 * π / 180 < π / 2
      nlinarith [pi_pos]
  field_simp [h_pos1, h_pos2, h_pos4, h_pos5, h_pos6]
  <;> ring_nf <;> field_simp [Real.sin_sq, Real.cos_sq, mul_pos, h_pos1, h_pos2, h_pos4, h_pos5, h_pos6, h_pos7]
  <;> nlinarith [Real.sin_sq_add_cos_sq (5 * π / 180), Real.sin_sq_add_cos_sq (20 * π / 180), Real.sin_sq_add_cos_sq (25 * π / 180), Real.sin_sq_add_cos_sq (5 * π / 180 + 20 * π / 180), Real.sin_le_one (5 * π / 180), Real.sin_le_one (20 * π / 180), Real.sin_le_one (25 * π / 180), Real.sin_le_one (5 * π / 180 + 20 * π / 180), Real.cos_le_one (5 * π / 180), Real.cos_le_one (20 * π / 180), Real.cos_le_one (25 * π / 180), Real.cos_le_one (5 * π / 180 + 20 * π / 180)]