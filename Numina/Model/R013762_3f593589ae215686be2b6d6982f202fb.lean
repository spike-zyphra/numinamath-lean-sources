import Mathlib

theorem algebra_1205 {a b : ℝ} (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) :
    b ^ a = 243 := by

  have ha : a = (5 : ℝ) := by
    have h2 : (2 : ℝ) ^ (a) = 32 := h₀
    have h3 : a = Real.logb 2 32 := by 
      rw [←h2]
      field_simp [Real.logb_rpow]
    rw [h3]
    have h4 : Real.logb 2 32 = (5 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h4]
  
  have h5 : (5 : ℝ) ^ b = 125 := by
    rw [show a = 5 by linarith [ha] ] at h₁
    norm_num at h₁ ⊢
    all_goals linarith
  
  have hb : b = (3 : ℝ) := by
    have h6 : (5 : ℝ) ^ b = 125 := h5
    have h7 : b = Real.logb 5 125 := by
      rw [←h6]
      field_simp [Real.logb_rpow]
    rw [h7]
    have h8 : Real.logb 5 125 = (3 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h8]

  rw [hb, ha]
  norm_num