import Mathlib

open Real

theorem algebra_162963 : 1 / tan (70 * π / 180) + 4 * cos (70 * π / 180) = sqrt 3 := by
  have htan : tan (70 * π / 180) = sin (70 * π / 180) / cos (70 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  have h1 : cos (70 * π / 180) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have h2 : sin (70 * π / 180) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : sin (70 * π / 180) ^ 2 + cos (70 * π / 180) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (70 * π / 180)
  field_simp [show sin (70 * π / 180) ≠ 0 by linarith [h2], show cos (70 * π / 180) ≠ 0 by linarith [h1]]
  have h5 : cos (70 * π / 180) = sin (20 * π / 180) := by
    have h6 : 70 * π / 180 = Real.pi / 2 - 20 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h6]
    rw [cos_pi_div_two_sub]
  have h7 : sin (70 * π / 180) = cos (20 * π / 180) := by
    have h8 : 70 * π / 180 = Real.pi / 2 - 20 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h8]
    rw [sin_pi_div_two_sub]
  rw [h5, h7]
  have h8 : sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) = Real.sqrt 3 * cos (20 * π / 180) := by
    have h14 : sin (40 * π / 180) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
      have h15 : 40 * π / 180 = 2 * (20 * π / 180) := by ring
      rw [h15]
      rw [sin_two_mul]
    have h17 : sin (40 * π / 180) = sin (60 * π / 180 - 20 * π / 180) := by
      ring_nf
    have h18 : sin (60 * π / 180 - 20 * π / 180) = sin (60 * π / 180) * cos (20 * π / 180) - cos (60 * π / 180) * sin (20 * π / 180) := by
      rw [sin_sub]
    have h19 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
      have h19 : 60 * π / 180 = Real.pi / 3 := by 
        linarith [Real.pi_pos]
      rw [h19]
      rw [sin_pi_div_three]
    have h20 : cos (60 * π / 180) = 1 / 2 := by 
      have h20 : 60 * π / 180 = Real.pi / 3 := by 
        linarith [Real.pi_pos]
      rw [h20]
      rw [cos_pi_div_three]
    rw [h17, h18, h19, h20] at h14
    nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num), Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sin_sq_add_cos_sq (20 * π / 180)]
  nlinarith