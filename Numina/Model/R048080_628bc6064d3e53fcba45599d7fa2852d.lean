import Mathlib

theorem algebra_189474 (a : ℝ) (h : Real.logb 6 2 = a) :
    Real.logb 3 6 = 1 / (1 - a) := by

  have h1 : Real.logb 3 6 = Real.logb 6 6 / Real.logb 6 3 := by
    field_simp [Real.logb]

  have h2 : Real.logb 6 6 = 1 := by 
    rw [Real.logb_self_eq_one]
    all_goals norm_num

  have h3 : Real.logb 6 3 = 1 - a := by
    have h4 : Real.logb 6 3 = Real.logb 6 6 - Real.logb 6 2 := by 
      rw [← Real.logb_div (by norm_num) (by norm_num)]
      all_goals norm_num 
    rw [h4]
    have h5 : Real.logb 6 6 = 1 := by 
      rw [Real.logb_self_eq_one]
      all_goals norm_num 
    rw [h5]
    linarith [h]

  rw [h1]
  rw [h2, h3]