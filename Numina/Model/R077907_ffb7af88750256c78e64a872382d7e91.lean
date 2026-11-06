import Mathlib

theorem algebra_21185 (h : Real.logb 3 6 = 1.63) : Real.logb 9 4 = 0.63 := by
  have h1 : Real.logb 9 4 = Real.logb 3 4 / Real.logb 3 9 := by
    field_simp [Real.logb]
    all_goals linarith
  have h2 : Real.logb 3 9 = 2 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
  have h3 : Real.logb 3 4 = 2 * Real.logb 3 2 := by
    have h4 : Real.logb 3 4 = Real.logb 3 (2^2) := by 
      norm_num
    rw [h4]
    simp [Real.logb_pow]
    all_goals linarith
  have h5 : Real.logb 3 6 = Real.logb 3 2 + 1 := by
    have h6 : Real.logb 3 6 = Real.logb 3 (2 * 3) := by 
      norm_num
    rw [h6]
    rw [Real.logb_mul (by norm_num) (by norm_num)]
    simp [Real.logb_self_eq_one]
    all_goals norm_num
  have h6 : Real.logb 3 2 = 0.63 := by 
    linarith [h, h5]
  rw [h1]
  rw [h3, h2, h6]
  all_goals norm_num