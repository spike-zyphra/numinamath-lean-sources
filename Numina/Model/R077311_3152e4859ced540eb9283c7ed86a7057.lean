import Mathlib

theorem algebra_13129 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : Real.logb 2 a + Real.logb 4 b = 8) (h₂ : Real.logb 4 a + Real.logb 8 b = 2) :
    Real.logb 8 a + Real.logb 2 b = -52 / 3 := by
  have h1 : Real.logb 4 b = Real.logb 2 b / 2 := by
    have h2 : Real.logb 4 b = Real.logb 2 b / Real.logb 2 (4 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h2, h3]
  
  have h1' : Real.logb 8 b = Real.logb 2 b / 3 := by
    have h2 : Real.logb 8 b = Real.logb 2 b / Real.logb 2 (8 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 2 (8 : ℝ) = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h2, h3]

  have h3 : Real.logb 4 a = Real.logb 2 a / 2 := by
    have h2 : Real.logb 4 a = Real.logb 2 a / Real.logb 2 (4 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h2, h3]

  have h3' : Real.logb 8 a = Real.logb 2 a / 3 := by
    have h2 : Real.logb 8 a = Real.logb 2 a / Real.logb 2 (8 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 2 (8 : ℝ) = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h2, h3]

  have eq1 : Real.logb 2 a + Real.logb 2 b / 2 = 8 := by
    rw [h1] at h₁
    linarith

  have eq2 : Real.logb 2 a / 2 + Real.logb 2 b / 3 = 2 := by
    rw [h3, h1'] at h₂
    linarith
  
  have eq3 : 2 * Real.logb 2 a + Real.logb 2 b = 16 := by
    linarith [eq1]

  have eq4 : 3 * Real.logb 2 a + 2 * Real.logb 2 b = 12 := by
    linarith [eq2]

  have h5 : Real.logb 2 a = 20 := by
    nlinarith

  have h6 : Real.logb 2 b = -24 := by
    linarith [eq3, h5]

  have h7 : Real.logb 8 a = Real.logb 2 a / 3 := h3'

  have h8 : Real.logb 8 a + Real.logb 2 b = (Real.logb 2 a / 3) + Real.logb 2 b := by
    rw [h7]

  rw [h8]
  rw [h5, h6]
  all_goals norm_num