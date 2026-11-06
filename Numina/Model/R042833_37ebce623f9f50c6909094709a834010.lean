import Mathlib

theorem inequalities_229405 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    b * 2 ^ a + a * 2 ^ (-b) ≥ a + b := by

  have h1 : (2 : ℝ) ^ a ≥ 1 + a * (Real.log 2) := by 
    have h2 : (2 : ℝ) ^ a = Real.exp (a * Real.log 2) := by
      rw [Real.rpow_def_of_pos]
      field_simp
      all_goals linarith 
    rw [h2]
    have h3 : Real.exp (a * Real.log 2) ≥ 1 + a * Real.log 2 := by 
      linarith [Real.add_one_le_exp (a * Real.log 2)]
    linarith

  have h4 : (2 : ℝ) ^ (-b : ℝ) ≥ 1 - b * (Real.log 2) := by
    have h5 : (2 : ℝ) ^ (-b : ℝ) = Real.exp (-b * Real.log 2) := by 
      rw [Real.rpow_def_of_pos]
      field_simp
      all_goals linarith 
    rw [h5]
    have h6 : Real.exp (-b * Real.log 2) ≥ 1 + (-b * Real.log 2) := by 
      linarith [Real.add_one_le_exp (-b * Real.log 2)]
    have h7 : 1 + (-b * Real.log 2) = 1 - b * (Real.log 2) := by 
      ring
    linarith [h6, h7]

  have h8 : b * ((2 : ℝ) ^ a) ≥ b * (1 + a * (Real.log 2)) := by 
    apply mul_le_mul_of_nonneg_left 
    linarith [h1]
    all_goals linarith 

  have h9 : a * ((2 : ℝ) ^ (-b : ℝ)) ≥ a * (1 - b * (Real.log 2)) := by 
    apply mul_le_mul_of_nonneg_left 
    linarith [h4]
    all_goals linarith

  have h10 : b * ((2 : ℝ) ^ a) + a * ((2 : ℝ) ^ (-b : ℝ)) ≥ b * (1 + a * (Real.log 2)) + a * (1 - b * (Real.log 2)) := by 
    linarith [h8, h9]

  have h11 : b * (1 + a * (Real.log 2)) + a * (1 - b * (Real.log 2)) = a + b := by 
    have h12 : Real.log 2 > 0 := by
      apply Real.log_pos 
      all_goals linarith 
    nlinarith

  linarith [h10, h11]