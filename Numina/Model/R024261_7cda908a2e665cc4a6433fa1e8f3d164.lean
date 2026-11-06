import Mathlib

theorem algebra_182477 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 2^b = 8) (h2 : a^b = 2) :
    a ^ (Real.logb 2 a) * 2^(b^2) = 128 := by

  have ha1 : a = 8 / (2 ^ b) := by 
    field_simp
    linarith

  have ha2 : a = (2 : ℝ) ^ (3 - b) := by
    rw [ha1]
    have h3 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h3]
    have h4 : (2 ^ b : ℝ) = (2 : ℝ) ^ b := by norm_num
    rw [h4]
    rw [← Real.rpow_sub]
    ring_nf
    all_goals linarith
  
  have ha3 : a ^ b = 2 := h2
  rw [show a = (2 : ℝ) ^ (3 - b) by linarith [ha2] ] at ha3
  have h5 : ((2 : ℝ) ^ (3 - b) ) ^ b = (2 : ℝ) ^ ( (3 - b) * b ) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith

  rw [h5] at ha3
  
  have h6 : (3 - b) * b = (1 : ℝ) := by
    apply_fun (Real.logb 2) at ha3
    have h7 : Real.logb 2 ((2 : ℝ) ^ ((3 - b) * b)) = Real.logb 2 2 := by 
      linarith [ha3]
    have h8 : Real.logb 2 ((2 : ℝ) ^ ((3 - b) * b)) = ( (3 - b) * b ) := by 
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    have h9 : Real.logb 2 (2 : ℝ) = 1 := by 
      norm_num

    rw [h8, h9] at h7 
    linarith
  
  have hlog : Real.logb 2 a = 3 - b := by 
    rw [ha2]
    have h10 : Real.logb 2 ((2 : ℝ) ^ (3 - b)) = (3 - b : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    linarith [h10]

  have hexp : (3 - b)^2 + b^2 = (7 : ℝ) := by 
    nlinarith [h6]

  have eq1 : a ^ (Real.logb 2 a) * 2 ^ (b ^ 2) = (2 : ℝ) ^ ((3 - b) ^ 2 + b ^ 2) := by
    have h7 : a ^ (Real.logb 2 a) = (2 : ℝ) ^ ( (3 - b ) ^ 2 ) := by 
      rw [show Real.logb 2 a = (3 - b) by linarith [hlog] ]
      rw [show a = (2 : ℝ) ^ (3 - b) by linarith [ha2] ]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h8 : (2 : ℝ) ^ ((3 - b) ^ 2 + b ^ 2) = (2 : ℝ) ^ ( (3 - b ) ^ 2 ) * (2 : ℝ) ^ ( b ^ 2 ) := by 
      rw [← Real.rpow_add]
      ring_nf
      all_goals linarith

    calc
      a ^ (Real.logb 2 a) * 2 ^ (b ^ 2) = (2 : ℝ) ^ ( (3 - b ) ^ 2 ) * (2 : ℝ) ^ ( b ^ 2 ) := by 
        rw [h7]
      _ = (2 : ℝ) ^ ((3 - b) ^ 2 + b ^ 2) := by 
        rw [h8]

  rw [eq1]

  rw [show (3 - b ) ^ 2 + b ^ 2 = (7 : ℝ) by linarith [hexp] ]
  norm_num