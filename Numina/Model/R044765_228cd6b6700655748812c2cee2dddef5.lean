import Mathlib

theorem number_theory_174643 : (Real.logb 10 2) ∈ Set.Ioo (3 / 10) (4 / 13) := by 
  have h1 : (3 / 10 : ℝ) < Real.logb 10 2 := by 
    have h4 : Real.logb 10 2 = Real.log (2) / Real.log (10) := by 
      field_simp [Real.logb]
    rw [h4] 
    have h7 : Real.log (2 : ℝ) / Real.log (10 : ℝ) > (3 / 10 : ℝ) := by 
      have h8 : Real.log (1000 : ℝ) = (3 : ℝ) * Real.log (10 : ℝ) := by 
        calc 
          Real.log (1000 : ℝ) = Real.log (10 ^ 3) := by norm_num 
          _ = (3 : ℝ) * Real.log (10 : ℝ) := by simp [Real.log_pow]
          _ = (3 : ℝ) * Real.log (10 : ℝ) := by ring
      have h9 : Real.log (1024 : ℝ) = (10 : ℝ) * Real.log (2 : ℝ) := by 
        calc 
          Real.log (1024 : ℝ) = Real.log (2 ^ 10) := by norm_num 
          _ = (10 : ℝ) * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h11 : Real.log (1000 : ℝ) < Real.log (1024 : ℝ) := by 
        apply Real.log_lt_log 
        all_goals norm_num 
      have h12 : (3 : ℝ) * Real.log (10 : ℝ) < (10 : ℝ) * Real.log (2 : ℝ) := by 
        linarith [h8, h9, h11]
      have h13 : Real.log (10 : ℝ) > 0 := by 
        apply Real.log_pos 
        all_goals norm_num 
      have h14 : Real.log (2 : ℝ) / Real.log (10 : ℝ) > (3 / 10 : ℝ) := by 
        have h15 : Real.log (2 : ℝ) / Real.log (10 : ℝ) > (3 / 10 : ℝ) := by 
          apply (lt_div_iff₀ (by linarith)).mpr 
          nlinarith [h12, h13]
        linarith 
      linarith 
    linarith 
  -- Second part: show Real.logb 10 2 < 4/13
  have h2 : Real.logb 10 2 < (4 / 13 : ℝ) := by 
    have h4 : Real.logb 10 2 = Real.log (2) / Real.log (10) := by 
      field_simp [Real.logb]
    rw [h4] 
    have h7 : Real.log (2 : ℝ) / Real.log (10 : ℝ) < (4 / 13 : ℝ) := by 
      have h19 : Real.log (8192 : ℝ) = (13 : ℝ) * Real.log (2 : ℝ) := by 
        calc 
          Real.log (8192 : ℝ) = Real.log (2 ^ 13) := by norm_num 
          _ = (13 : ℝ) * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h20 : Real.log (10000 : ℝ) = (4 : ℝ) * Real.log (10 : ℝ) := by 
        calc 
          Real.log (10000 : ℝ) = Real.log (10 ^ 4) := by norm_num 
          _ = (4 : ℝ) * Real.log (10 : ℝ) := by simp [Real.log_pow]
      have h21 : Real.log (8192 : ℝ) < Real.log (10000 : ℝ) := by 
        apply Real.log_lt_log 
        all_goals norm_num 
      -- Now combine these to show that 13 * Real.log 2 < 4 * Real.log 10
      have h22 : (13 : ℝ) * Real.log (2 : ℝ) < (4 : ℝ) * Real.log (10 : ℝ) := by 
        linarith [h19, h20, h21]
      have h13 : Real.log (10 : ℝ) > 0 := by 
        apply Real.log_pos 
        all_goals norm_num 
      have h24 : Real.log (2 : ℝ) / Real.log (10 : ℝ) < (4 / 13 : ℝ) := by 
        apply (div_lt_iff₀ (by linarith)).mpr 
        nlinarith [h22, h13]
      linarith 
    linarith 
  exact ⟨h1, h2⟩