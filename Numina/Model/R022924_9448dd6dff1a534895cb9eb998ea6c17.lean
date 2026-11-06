import Mathlib

theorem algebra_770 (X Y Z : ℝ) (h₁ : Real.logb 6 10 = X) (h₂ : Real.logb 6 7 = Y) (h₃ : Real.logb 6 4 = Z) :
    Real.logb 6 (1/9) = Z - 2 := by

  have h4 : Real.logb 6 (1 / 9) = Real.logb 6 1 - Real.logb 6 9 := by 
    rw [← Real.logb_div (by norm_num) (by norm_num)]
    all_goals norm_num
  
  have h5 : Real.logb 6 1 = 0 := by
    simp [Real.logb_one]
  
  have h6 : Real.logb 6 9 = 2 * Real.logb 6 3 := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num]
    simp [Real.logb_pow]
  
  have h7 : Real.logb 6 3 = 1 - Real.logb 6 2 := by
    have h8 : Real.logb 6 3 = Real.logb 6 6 - Real.logb 6 2 := by
      have h9 : Real.logb 6 3 = Real.logb 6 (6 / 2) := by 
        norm_num
      have h10 : Real.logb 6 (6 / 2) = Real.logb 6 6 - Real.logb 6 2 := by
        rw [Real.logb_div (by norm_num) (by norm_num)]
      linarith [h9, h10]
    have h9 : Real.logb 6 6 = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith [h8, h9]

  have h10 : Real.logb 6 4 = 2 * Real.logb 6 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    simp [Real.logb_pow]

  have h11 : Real.logb 6 2 = Z / 2 := by
    linarith [h₃, h10]

  have h12 : Real.logb 6 3 = 1 - Z / 2 := by
    rw [h7, h11]
    all_goals linarith
  
  have h13 : Real.logb 6 9 = 2 - Z := by 
    rw [h6, h12]
    all_goals linarith
  
  rw [h4, h5]
  linarith [h13]