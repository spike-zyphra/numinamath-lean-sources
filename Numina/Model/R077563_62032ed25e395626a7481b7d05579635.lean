import Mathlib

theorem algebra_179929 {a b : ℝ} (ha : Real.logb 10 5 = a) (hb : Real.logb 10 3 = b) :
    Real.logb 30 8 = 3 * (1 - a) / (b + 1) := by
  have h1 : Real.logb 30 8 = Real.logb 10 8 / Real.logb 10 30 := by 
    field_simp [Real.logb]
    all_goals linarith
  have h2 : Real.logb 10 8 = 3 * Real.logb 10 2 := by 
    calc 
      Real.logb 10 8 = Real.logb 10 (2 ^ 3) := by norm_num
      _ = 3 * Real.logb 10 2 := by simp [Real.logb_pow]
  have h3 : Real.logb 10 2 = 1 - a := by 
    have h4 : Real.logb 10 5 = a := ha
    have h5 : Real.logb 10 2 + Real.logb 10 5 = 1 := by 
      have h6 : Real.logb 10 2 + Real.logb 10 5 = Real.logb 10 (2 * 5) := by 
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      rw [h6]
      norm_num [Real.logb_self_eq_one]
      all_goals linarith
    rw [h4] at h5
    linarith
  have h8 : Real.logb 10 30 = b + 1 := by 
    have h7a : Real.logb 10 30 = Real.logb 10 3 + 1 := by 
      have h8 : Real.logb 10 30 = Real.logb 10 (3 * 10) := by norm_num
      rw [h8]
      have h9 : Real.logb 10 (3 * 10) = Real.logb 10 3 + Real.logb 10 10 := by 
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      rw [h9]
      have h10 : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
      rw [h10]
      all_goals norm_num
    have h7b : Real.logb 10 3 = b := hb
    rw [h7a, h7b]
    all_goals norm_num
  have h9 : Real.logb 10 8 = 3 * (1 - a) := by 
    rw [h2]
    rw [h3]
    all_goals linarith
  rw [h1, h9, h8]
  all_goals norm_num