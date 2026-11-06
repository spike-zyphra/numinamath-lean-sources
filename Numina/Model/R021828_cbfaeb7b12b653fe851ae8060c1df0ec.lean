import Mathlib

theorem algebra_127685 {x a : ℝ} (ha : 1 < a) (hx : 0 < x ∧ x ≠ 1) (h : Real.logb x a = a) :
    x = 10 ^ (Real.logb 10 a / a) := by
  have h1 : x ^ a = a := by 
    have h2 : Real.logb x a = a := h 
    have h3 : x ^ a = a := by 
      rw [←h2]
      field_simp [Real.rpow_logb, hx.1, hx.2, show 0 < a by linarith] at *
      all_goals linarith
    linarith
  have h4 : x = a ^ (1 / a) := by 
    have h5 : x ^ a = a := h1 
    have h6 : x = (x ^ a) ^ (1 / a) := by 
      rw [← Real.rpow_mul]
      field_simp
      all_goals linarith 
    rw [show x ^ a = a by linarith [h1]] at h6 
    linarith
  rw [h4]
  have h7 : a ^ (1 / a) = 10 ^ (Real.logb 10 a / a) := by 
    have h8 : Real.logb 10 (a ^ (1 / a)) = Real.logb 10 a / a := by 
      have h9 : Real.logb 10 (a ^ (1 / a)) = (1 / a) * Real.logb 10 a := by 
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals linarith 
      rw [show (1 / a) * Real.logb 10 a = Real.logb 10 a / a by ring] at h9 
      linarith 
    have h9 : a ^ (1 / a) = (10 : ℝ) ^ (Real.logb 10 a / a) := by 
      have h10a1 : a ^ (1 / a) > 0 := by positivity 
      have h10a2 : (10 : ℝ) ^ (Real.logb 10 a / a) > 0 := by 
        apply Real.rpow_pos_of_pos 
        all_goals norm_num 
      have h11 : Real.logb 10 (a ^ (1 / a)) = Real.logb 10 ((10 : ℝ) ^ (Real.logb 10 a / a)) := by 
        rw [h8]
        have h10a3 : Real.logb 10 ((10 : ℝ) ^ (Real.logb 10 a / a)) = Real.logb 10 a / a := by 
          rw [Real.logb_rpow]
          all_goals 
            try norm_num 
            try linarith 
        linarith [h10a3]
      have h14' : a ^ (1 / a) = (10 : ℝ) ^ (Real.logb 10 a / a) := by 
        apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h10a1) (Set.mem_Ioi.mpr h10a2) h11 
      linarith [h14']
    simpa using h9
  exact h7