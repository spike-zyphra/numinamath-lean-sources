import Mathlib

theorem algebra_306399 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : Real.logb 8 a + Real.logb 4 (b ^ 2) = 5) (h2 : Real.logb 8 b + Real.logb 4 (a ^ 2) = 7) :
    a * b = 512 := by
  have h1' : Real.logb 8 a = Real.logb 2 a / 3 := by
    have h1 : Real.logb 8 a = Real.logb 2 a / Real.logb 2 8 := by 
      field_simp [Real.logb]
      all_goals linarith
    have h2 : Real.logb 2 8 = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      all_goals norm_num
    rw [h1, h2]
    all_goals norm_num
  have h1'' : Real.logb 4 (b ^ 2) = Real.logb 2 b := by
    have h1 : Real.logb 4 (b ^ 2) = Real.logb 2 (b ^ 2) / Real.logb 2 4 := by 
      field_simp [Real.logb]
      all_goals linarith
    have h2 : Real.logb 2 (b ^ 2) = 2 * Real.logb 2 b := by 
      simp [Real.logb_pow]
      all_goals linarith
    have h3 : Real.logb 2 4 = 2 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      all_goals norm_num
    rw [h1, h2, h3]
    all_goals ring
  rw [h1', h1''] at h1
  have h2' : Real.logb 8 b = Real.logb 2 b / 3 := by 
    have h1 : Real.logb 8 b = Real.logb 2 b / Real.logb 2 8 := by 
      field_simp [Real.logb]
      all_goals linarith
    have h2 : Real.logb 2 8 = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      all_goals norm_num
    rw [h1, h2]
  have h2'' : Real.logb 4 (a ^ 2) = Real.logb 2 a := by 
    have h1 : Real.logb 4 (a ^ 2) = Real.logb 2 (a ^ 2) / Real.logb 2 4 := by 
      field_simp [Real.logb]
      all_goals linarith
    have h2 : Real.logb 2 (a ^ 2) = 2 * Real.logb 2 a := by 
      simp [Real.logb_pow]
      all_goals linarith
    have h3 : Real.logb 2 4 = 2 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      all_goals norm_num
    rw [h1, h2, h3]
    all_goals ring
  rw [h2', h2''] at h2
  have eq1 := h1
  have eq2 := h2
  have eq3 : Real.logb 2 a + 3 * Real.logb 2 b = 15 := by 
    linarith [eq1]
  have eq4 : 3 * Real.logb 2 a + Real.logb 2 b = 21 := by 
    linarith [eq2]
  have h3 : Real.logb 2 a = 6 := by 
    linarith [eq3, eq4]
  have h4 : Real.logb 2 b = 3 := by 
    linarith [eq3, h3]
  have ha' : a = (2 : ℝ) ^ (6 : ℝ) := by 
    have h5 : a = (2 : ℝ) ^ (Real.logb 2 a : ℝ) := by 
      field_simp [Real.rpow_logb, show (2 : ℝ) > 0 by norm_num, show (2 : ℝ) ≠ 1 by norm_num, show (0 : ℝ) < a by linarith]
      all_goals linarith
    rw [h5, h3]
    all_goals norm_num
  have hb' : b = (2 : ℝ) ^ (3 : ℝ) := by 
    have h6 : b = (2 : ℝ) ^ (Real.logb 2 b : ℝ) := by 
      field_simp [Real.rpow_logb, show (2 : ℝ) > 0 by norm_num, show (2 : ℝ) ≠ 1 by norm_num, show (0 : ℝ) < b by linarith]
      all_goals linarith
    rw [h6, h4]
    all_goals norm_num
  rw [ha', hb']
  have h7 : ((2 : ℝ) ^ (6 : ℝ)) * ((2 : ℝ) ^ (3 : ℝ)) = (2 : ℝ) ^ (9 : ℝ) := by 
    rw [← Real.rpow_add]
    norm_num
    all_goals norm_num
  rw [h7]
  norm_num