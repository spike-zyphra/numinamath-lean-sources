import Mathlib

theorem algebra_199675 : 15 * Real.tan (44 * Real.pi / 180) * Real.tan (45 * Real.pi / 180) * Real.tan (46 * Real.pi / 180) = 15 := by 
  have htan1 : Real.tan (45 * Real.pi / 180) = 1 := by 
    have h1 : 45 * Real.pi / 180 = Real.pi / 4 := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [Real.tan_eq_sin_div_cos]
    have h2 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four 
    have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four 
    rw [h2, h3]
    field_simp 
    <;> nlinarith 
  have htan2 : Real.tan (46 * Real.pi / 180) = 1 / Real.tan (44 * Real.pi / 180) := by 
    have h1 : 46 * Real.pi / 180 = Real.pi / 2 - 44 * Real.pi / 180 := by 
      nlinarith [Real.pi_pos]
    rw [h1]
    have htan2 : Real.tan (Real.pi / 2 - 44 * Real.pi / 180) = 1 / Real.tan (44 * Real.pi / 180) := by 
      rw [Real.tan_eq_sin_div_cos]
      have htan3 : Real.sin (Real.pi / 2 - 44 * Real.pi / 180) = Real.cos (44 * Real.pi / 180) := by 
        rw [Real.sin_pi_div_two_sub]
      have htan4 : Real.cos (Real.pi / 2 - 44 * Real.pi / 180) = Real.sin (44 * Real.pi / 180) := by 
        rw [Real.cos_pi_div_two_sub]
      rw [htan3, htan4]
      field_simp [Real.tan_eq_sin_div_cos]
      <;> nlinarith [Real.sin_sq_add_cos_sq (44 * Real.pi / 180)]
    exact htan2
  rw [htan1, htan2]
  have htan3 : Real.tan (44 * Real.pi / 180) ≠ 0 := by 
    by_contra h1
    have htan4 : Real.tan (44 * Real.pi / 180) = Real.sin (44 * Real.pi / 180) / Real.cos (44 * Real.pi / 180) := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan4] at h1 
    have htan5 : Real.sin (44 * Real.pi / 180) > 0 := by 
      apply Real.sin_pos_of_pos_of_lt_pi 
      · -- Show $0 < 44^\circ$ in radians 
        nlinarith [Real.pi_pos]
      · -- Show $44^\circ < \pi$ in radians 
        nlinarith [Real.pi_pos]
    have htan6 : Real.sin (44 * Real.pi / 180) ≠ 0 := by 
      linarith 
    have htan7 : Real.sin (44 * Real.pi / 180) = 0 := by 
      field_simp [(show Real.cos (44 * Real.pi / 180) ≠ 0 by 
        have h5 : Real.cos (44 * Real.pi / 180) > 0 := by 
          apply Real.cos_pos_of_mem_Ioo 
          constructor 
          · nlinarith [Real.pi_pos] 
          · nlinarith [Real.pi_pos]
        linarith 
      )] at h1 ⊢ 
      <;> nlinarith
    contradiction 
  field_simp [htan3]
  <;> nlinarith [Real.sin_sq_add_cos_sq (44 * Real.pi / 180)]