import Mathlib

open Real Set
open scoped Real

theorem algebra_318889 :
  sqrt (1 - 2 * sin (20 * π / 180) * cos (20 * π / 180)) /
  (cos (20 * π / 180) - sqrt (1 - (cos (160 * π / 180))^2)) = 1 := by
  have h1 : sin (160 * π / 180) = sin (20 * π / 180) := by
    have h2 : 160 * π / 180 = π - 20 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_sub]
  have h3 : cos (160 * π / 180) = -cos (20 * π / 180) := by
    have h4 : 160 * π / 180 = π - 20 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [cos_pi_sub]
  have h4 : sqrt (1 - (cos (160 * π / 180))^2) = sin (20 * π / 180) := by
    have h5 : 1 - (cos (160 * π / 180))^2 = (sin (20 * π / 180))^2 := by
      have h7 : cos (160 * π / 180) = -cos (20 * π / 180) := h3
      rw [h7]
      nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180)]
    have h6 : sin (20 * π / 180) ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi 
      all_goals linarith [Real.pi_pos] 
    rw [h5] 
    have h7 : sqrt ((sin (20 * π / 180))^2) = sin (20 * π / 180) := by 
      apply Real.sqrt_sq (by linarith) 
    rw [h7] 
  have h5 : sqrt (1 - 2 * sin (20 * π / 180) * cos (20 * π / 180)) = cos (20 * π / 180) - sin (20 * π / 180) := by
    have h6 : 1 - 2 * sin (20 * π / 180) * cos (20 * π / 180) = (cos (20 * π / 180) - sin (20 * π / 180))^2 := by
      nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180)]
    have h7 : sqrt ((cos (20 * π / 180) - sin (20 * π / 180))^2) = abs (cos (20 * π / 180) - sin (20 * π / 180)) := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h6, h7]
    have h8 : cos (20 * π / 180) - sin (20 * π / 180) ≥ 0 := by
      have h20 : cos (20 * π / 180) > sin (20 * π / 180) := by
        have h18 : cos (20 * π / 180) > 0 := by 
          apply cos_pos_of_mem_Ioo 
          constructor 
          · linarith [Real.pi_pos] 
          · linarith [Real.pi_pos]
        have h16 : sin (20 * π / 180) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          all_goals linarith [Real.pi_pos] 
        have h19 : cos (20 * π / 180) - sin (20 * π / 180) > 0 := by
          have h116 : 20 * π / 180 < π / 4 := by 
            nlinarith [Real.pi_pos] 
          have h170 : cos (20 * π / 180) > cos (π / 4) := by
            apply Real.cos_lt_cos_of_nonneg_of_le_pi
            all_goals 
              nlinarith [Real.pi_pos] 
          have h171 : cos (π / 4) = sin (π / 4) := by
            have h72 : cos (π / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
            have h73 : sin (π / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
            rw [h72, h73] 
          have h172 : sin (π / 4) > 0 := by
            apply sin_pos_of_pos_of_lt_pi
            all_goals 
              nlinarith [Real.pi_pos] 
          have h173 : sin (20 * π / 180) < sin (π / 4) := by
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals
              nlinarith [Real.pi_pos] 
          nlinarith 
        linarith 
      linarith 
    rw [abs_of_nonneg (by linarith)]
  have h6 : cos (20 * π / 180) - sin (20 * π / 180) ≠ 0 := by
    have h20 : cos (20 * π / 180) > sin (20 * π / 180) := by
      have h18 : cos (20 * π / 180) > 0 := by 
        apply cos_pos_of_mem_Ioo 
        constructor 
        · linarith [Real.pi_pos] 
        · linarith [Real.pi_pos] 
      have h16 : sin (20 * π / 180) > 0 := by 
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith [Real.pi_pos] 
      have h19 : cos (20 * π / 180) - sin (20 * π / 180) > 0 := by
        have h116 : 20 * π / 180 < π / 4 := by 
          nlinarith [Real.pi_pos] 
        have h170 : cos (20 * π / 180) > cos (π / 4) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals 
            nlinarith [Real.pi_pos] 
        have h171 : cos (π / 4) = sin (π / 4) := by
          have h72 : cos (π / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
          have h73 : sin (π / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
          rw [h72, h73] 
        have h172 : sin (π / 4) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          all_goals 
            nlinarith [Real.pi_pos] 
        have h173 : sin (20 * π / 180) < sin (π / 4) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            nlinarith [Real.pi_pos] 
        nlinarith 
      linarith 
    linarith 
  rw [h5, h4]
  field_simp [h6]