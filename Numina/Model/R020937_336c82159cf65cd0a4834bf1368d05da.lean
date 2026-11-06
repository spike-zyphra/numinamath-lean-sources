import Mathlib

open Real

theorem algebra_12815 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 4 → f x = (1 / 2) ^ x)
    (hf' : ∀ x, x < 4 → f x = f (x + 1)) :
    f (logb 2 3) = 1 / 24 := by

  have h1 : logb 2 3 < 4 := by
    have h2 : logb 2 3 < 2 := by
      have h3 : logb 2 3 < logb 2 4 := by
        apply Real.logb_lt_logb
        all_goals norm_num
      have h4 : logb 2 4 = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith [h3, h4]
    linarith
  have eq1 : f (logb 2 3) = f (logb 2 3 + 1) := by
    apply hf' 
    linarith [h1]
  
  have eq2 : logb 2 3 + 1 = logb 2 6 := by 
    have h3 : logb 2 6 = logb 2 (3 * 2) := by 
      norm_num 
    have h4 : logb 2 (3 * 2) = logb 2 3 + logb 2 2 := by 
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h5 : logb 2 2 = 1 := by 
      norm_num [Real.logb_self_eq_one]
    linarith [h3, h4, h5]
    
  have eq3 : f (logb 2 3 + 1) = f (logb 2 6) := by 
    rw [eq2]
    
  rw [eq1, eq3]
  
  have h2 : logb 2 6 < 4 := by 
    have h3 : logb 2 6 < 3 := by 
      have h4 : logb 2 6 < logb 2 8 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h5 : logb 2 8 = 3 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      linarith [h4, h5] 
    linarith 
  have eq4 : f (logb 2 6) = f (logb 2 6 + 1) := by 
    apply hf' 
    linarith [h2]
  
  have eq5 : logb 2 6 + 1 = logb 2 12 := by 
    have h3 : logb 2 12 = logb 2 (6 * 2) := by 
      norm_num 
    have h4 : logb 2 (6 * 2) = logb 2 6 + logb 2 2 := by 
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h5 : logb 2 2 = 1 := by 
      norm_num [Real.logb_self_eq_one]
    linarith [h3, h4, h5]
  
  have eq6 : f (logb 2 6 + 1) = f (logb 2 12) := by 
    rw [eq5]
  
  rw [eq4, eq6]
  
  have h3 : logb 2 12 < 4 := by 
    have h4 : logb 2 12 < 4 := by 
      have h5 : logb 2 12 < logb 2 16 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h6 : logb 2 16 = 4 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      linarith [h5, h6] 
    linarith 
  have eq7 : f (logb 2 12) = f (logb 2 12 + 1) := by 
    apply hf' 
    linarith [h3]
  
  have eq8 : logb 2 12 + 1 = logb 2 24 := by 
    have h3 : logb 2 24 = logb 2 (12 * 2) := by 
      norm_num 
    have h4 : logb 2 (12 * 2) = logb 2 12 + logb 2 2 := by 
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h5 : logb 2 2 = 1 := by 
      norm_num [Real.logb_self_eq_one]
    linarith [h3, h4, h5]
  
  have eq9 : f (logb 2 12 + 1) = f (logb 2 24) := by 
    rw [eq8]
  
  rw [eq7, eq9]
  
  have h4 : logb 2 24 ≥ 4 := by 
    have h5 : logb 2 24 > 4 := by 
      have h6 : logb 2 16 = 4 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      have h7 : logb 2 24 > logb 2 16 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      linarith [h6, h7] 
    linarith 
  have eq10 : f (logb 2 24) = (1 / 2) ^ logb 2 24 := by 
    apply hf 
    linarith [h4] 
  rw [eq10]
  have h7 : (1 / 2 : ℝ) ^ logb 2 24 = (1 / 24 : ℝ) := by
    have h8 : (1 / 2 : ℝ) ^ logb 2 24 = (2 : ℝ) ^ (- (logb 2 24) : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring 
      all_goals linarith
    rw [h8] 
    have h9 : - (logb 2 24) = logb 2 (24⁻¹) := by 
      have h10 : logb 2 (24⁻¹) = - (logb 2 (24)) := by 
        simp [Real.logb_inv]
      linarith [h10, show logb 2 (24) = logb 2 24 by rfl]
    rw [h9] 
    have h11 : (24 : ℝ)⁻¹ = (1 / 24 : ℝ) := by 
      norm_num 
    have h12 : (2 : ℝ) ^ (logb 2 (24⁻¹) : ℝ) = (24 : ℝ)⁻¹ := by 
      rw [Real.rpow_logb]
      all_goals norm_num 
    rw [h12, h11] 
  linarith [h7]