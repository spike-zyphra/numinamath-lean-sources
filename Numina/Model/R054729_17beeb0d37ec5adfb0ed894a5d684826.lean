import Mathlib

theorem algebra_268914 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : Real.logb 2 a + Real.logb 4 b = 8) (h₂ : Real.logb 4 a + Real.logb 8 b = 2) :
    Real.logb 8 a + Real.logb 2 b = -52 / 3 := by
  have h3 : Real.logb 4 b = Real.logb 2 b / 2 := by
    have h4 : Real.logb 4 b = Real.logb 2 b / Real.logb 2 4 := by
      field_simp [Real.logb]
    have h5 : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h4, h5]
  have h6 : Real.logb 8 b = Real.logb 2 b / 3 := by
    have h7 : Real.logb 8 b = Real.logb 2 b / Real.logb 2 8 := by 
      field_simp [Real.logb]
    have h8 : Real.logb 2 8 = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h7, h8]
  have h7 : Real.logb 4 a = Real.logb 2 a / 2 := by 
    have h8 : Real.logb 4 a = Real.logb 2 a / Real.logb 2 4 := by 
      field_simp [Real.logb]
    have h9 : Real.logb 2 4 = 2 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h8, h9]
  have h10 : Real.logb 8 a = Real.logb 2 a / 3 := by 
    have h11 : Real.logb 8 a = Real.logb 2 a / Real.logb 2 8 := by 
      field_simp [Real.logb]
    have h12 : Real.logb 2 8 = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h11, h12]
  have eq1 : Real.logb 2 a + Real.logb 2 b / 2 = 8 := by
    rw [h3] at h₁ 
    linarith 
  have eq2 : Real.logb 2 a / 2 + Real.logb 2 b / 3 = 2 := by
    rw [h7, h6] at h₂ 
    linarith 
  have h11 : Real.logb 2 a = 20 := by 
    linarith [eq1, eq2] 
  have h12 : Real.logb 2 b = -24 := by 
    linarith [eq1, h11] 
  have h13 : Real.logb 8 a = Real.logb 2 a / 3 := h10 
  have h14 : Real.logb 8 a = (20 : ℝ) / 3 := by 
    rw [h13, h11] 
    all_goals norm_num 
  have h15 : Real.logb 2 b = -24 := by 
    linarith [h12] 
  rw [h14, h15] 
  all_goals norm_num