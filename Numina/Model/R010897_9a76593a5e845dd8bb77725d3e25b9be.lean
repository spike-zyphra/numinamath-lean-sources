import Mathlib

open Real

theorem algebra_21388 {x : ℝ} (hx : x > 1) (h : logb 2 (logb 8 x) = logb 8 (logb 2 x)) :
    (logb 2 x)^2 = 27 := by 
  have h1 : logb 8 x = logb 2 x / 3 := by
    have h2 : logb 8 x = logb 2 x / logb 2 (8 : ℝ) := by 
      field_simp [logb]
    have h3 : logb 2 (8 : ℝ) = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2, h3]
  
  have h4 : logb 2 (logb 8 x) = logb 2 (logb 2 x / 3) := by 
    rw [h1]

  have h5 : logb 8 (logb 2 x) = (logb 2 (logb 2 x)) / 3 := by 
    have h6 : logb 8 (logb 2 x) = (logb 2 (logb 2 x)) / logb 2 (8 : ℝ) := by 
      field_simp [logb]
    have h7 : logb 2 (8 : ℝ) = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h6, h7]

  rw [h4, h5] at h

  have h6 : logb 2 (logb 2 x / 3) = logb 2 (logb 2 x) - logb 2 (3 : ℝ) := by 
    have h11 : logb 2 x > 0 := by
      apply logb_pos
      all_goals linarith
    have h12 : (3 : ℝ) > 0 := by norm_num
    rw [logb_div (by
      have h11 : logb 2 x > 0 := by
        apply logb_pos
        all_goals linarith
      have h12 : (3 : ℝ) > 0 := by norm_num
      positivity
    ) (by norm_num)]

  rw [h6] at h
  
  have h8 : 2 * logb 2 (logb 2 x) = 3 * logb 2 (3 : ℝ) := by
    linarith
  
  have h9 : 2 * logb 2 (logb 2 x) = logb 2 ((logb 2 x) ^ 2) := by
    simp [logb_pow]

  have h10 : 3 * logb 2 (3 : ℝ) = logb 2 ((3 : ℝ) ^ 3) := by 
    simp [logb_pow]

  have h11 : logb 2 ((logb 2 x) ^ 2) = logb 2 ((3 : ℝ) ^ 3) := by
    linarith [h8, h9, h10]

  have h12 : (logb 2 x) ^ 2 > 0 := by 
    have h13 : logb 2 x > 0 := by 
      apply logb_pos 
      all_goals linarith 
    positivity

  have h13 : (3 : ℝ) ^ 3 > 0 := by norm_num

  have h14 : (logb 2 x) ^ 2 = (3 : ℝ) ^ 3 := by
    apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h12) (Set.mem_Ioi.mpr h13) h11

  have h15 : (3 : ℝ) ^ 3 = (27 : ℝ) := by norm_num

  rw [h15] at h14
  linarith