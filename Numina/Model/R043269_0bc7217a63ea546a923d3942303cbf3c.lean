import Mathlib

open Real

theorem algebra_278679 {a b c : ℝ} (ha : a = logb 8 5) (hb : b = logb 4 3) (hc : c = 2 / 3) :
    b > a ∧ a > c := by 
  have ha2 : a = Real.logb 2 5 / 3 := by 
    rw [ha]
    have h1 : Real.logb 8 5 = Real.logb 2 5 / Real.logb 2 8 := by
      field_simp [Real.logb]
    rw [h1]
    have h2 : Real.logb 2 8 = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h2]
  
  have hb2 : b = Real.logb 2 3 / 2 := by
    rw [hb]
    have h1 : Real.logb 4 3 = Real.logb 2 3 / Real.logb 2 4 := by 
      field_simp [Real.logb]
    rw [h1]
    have h2 : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h2]
  
  have h1 : b > a := by
    rw [hb2, ha2]
    have h2 : 3 * (Real.logb 2 3) > 2 * (Real.logb 2 5) := by 
      have h3 : Real.logb 2 27 = 3 * Real.logb 2 3 := by 
        calc
          Real.logb 2 27 = Real.logb 2 (3 ^ 3) := by norm_num
          _ = 3 * (Real.logb 2 3) := by simp [Real.logb_pow]
      have h4 : Real.logb 2 25 = 2 * Real.logb 2 5 := by 
        calc 
          Real.logb 2 25 = Real.logb 2 (5 ^ 2) := by norm_num
          _ = 2 * (Real.logb 2 5) := by simp [Real.logb_pow]
      have h5 : Real.logb 2 27 > Real.logb 2 25 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num
      linarith [h3, h4, h5]
  
    linarith
  
  have h2 : a > c := by
    rw [ha2, hc]
    have h3 : Real.logb 2 5 > (2 : ℝ) := by 
      have h4 : Real.logb 2 5 > Real.logb 2 4 := by 
        apply Real.logb_lt_logb
        all_goals norm_num
      have h5 : Real.logb 2 4 = (2 : ℝ) := by 
        calc 
          Real.logb 2 4 = Real.logb 2 (2 ^ 2) := by norm_num
          _ = (2 : ℝ) * Real.logb 2 (2 : ℝ) := by simp [Real.logb_pow]
          _ = (2 : ℝ) * (1 : ℝ) := by simp [Real.logb_self_eq_one]
          _ = (2 : ℝ) := by norm_num
      linarith [h4, h5]
  
    linarith
  
  constructor 
  · exact h1 
  · exact h2