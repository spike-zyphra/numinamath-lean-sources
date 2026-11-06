import Mathlib

theorem algebra_1632
    {a b : ℝ}
    (ha : a = Real.logb 12 18)
    (hb : b = Real.logb 24 54) :
    a * b + 5 * (a - b) = 1 := by 
  have ha' : a = (Real.log 18) / (Real.log 12) := by
    rw [ha]
    have h : Real.logb 12 18 = Real.log 18 / Real.log 12 := by
      field_simp [Real.logb]
      all_goals norm_num
    linarith
  
  have hb' : b = (Real.log 54) / (Real.log 24) := by
    rw [hb]
    have h : Real.logb 24 54 = Real.log 54 / Real.log 24 := by
      field_simp [Real.logb]
      all_goals norm_num
    linarith
  
  have h1 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by 
    rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num]
    simp [Real.log_mul, Real.log_pow]
    all_goals linarith
  
  have h2 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by 
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num]
    simp [Real.log_mul, Real.log_pow]
    all_goals linarith
  
  have h3 : Real.log 54 = Real.log 2 + 3 * Real.log 3 := by 
    rw [show (54 : ℝ) = 2 * 3 ^ 3 by norm_num]
    simp [Real.log_mul, Real.log_pow]
    all_goals linarith
  
  have h4 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by 
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num]
    simp [Real.log_mul, Real.log_pow]
    all_goals linarith
  
  rw [ha', hb', h1, h2, h3, h4]
  
  -- convert b to variable substitution
  -- a = (ln 2 + 2 ln 3) / (2 ln 2 + ln 3)
  -- b = (ln 2 + 3 ln 3) / (3 ln 2 + ln 3)
  -- need to prove a * b + 5*(a - b) = 1

  have h7 : Real.log 2 > 0 := by
    apply Real.log_pos
    all_goals linarith
  
  have h8 : Real.log 3 > 0 := by
    apply Real.log_pos
    all_goals linarith
  
  field_simp [(show 2 * Real.log 2 + Real.log 3 ≠ 0 by
    nlinarith), (show 3 * Real.log 2 + Real.log 3 ≠ 0 by
    nlinarith)]
  <;> ring_nf
  <;> field_simp [(show 2 * Real.log 2 + Real.log 3 ≠ 0 by
    nlinarith), (show 3 * Real.log 2 + Real.log 3 ≠ 0 by
    nlinarith)]
  <;> ring_nf
  <;> nlinarith