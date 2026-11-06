import Mathlib

theorem algebra_9430 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.logb 2 a = Real.logb 3 b) (h' : Real.logb 3 b = Real.logb 6 5) :
    a * b = 5 := by
  have h1 : Real.logb 2 a = Real.logb 3 b := h
  have h2 : Real.logb 3 b = Real.logb 6 5 := h'
  have h3 : Real.logb 2 a = Real.logb 6 5 := by linarith
  have h4 : Real.logb 3 b = Real.logb 6 5 := by linarith

  have h5 : a = (2 : ℝ) ^ Real.logb 6 5 := by
    have h6 : Real.logb 2 a = Real.logb 6 5 := h3
    have h8 : a = (2 : ℝ) ^ Real.logb 2 a := by 
      field_simp at *
      all_goals nlinarith
    rw [show Real.logb 2 a = Real.logb 6 5 by linarith] at h8
    linarith

  have h6 : b = (3 : ℝ) ^ Real.logb 6 5 := by 
    have h7 : Real.logb 3 b = Real.logb 6 5 := h4
    have h8 : b = (3 : ℝ) ^ Real.logb 3 b := by 
      field_simp at *
      all_goals nlinarith
    rw [show Real.logb 3 b = Real.logb 6 5 by linarith] at h8
    linarith

  calc 
    a * b = (2 : ℝ) ^ Real.logb 6 5 * ((3 : ℝ) ^ Real.logb 6 5) := by rw [h5, h6]
    _ = ((2 : ℝ) * (3 : ℝ)) ^ Real.logb 6 5 := by 
      rw [← Real.mul_rpow]
      all_goals nlinarith
    _ = (6 : ℝ) ^ Real.logb 6 5 := by 
      norm_num
    _ = 5 := by 
      have h7 : (6 : ℝ) ^ Real.logb 6 5 = (5 : ℝ) := by 
        field_simp
      linarith