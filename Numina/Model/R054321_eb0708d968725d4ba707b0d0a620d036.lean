import Mathlib

theorem algebra_22543 {x : ℝ} (hx : 0 ≤ x) (h : Real.sqrt (x + 7) - Real.sqrt x = Real.sqrt 3) :
    x = 4 / 3 := by
  have h1 : Real.sqrt (x + 7) = Real.sqrt x + Real.sqrt 3 := by
    linarith
  
  have h2 : Real.sqrt (x + 7) ^ 2 = x + 7 := by 
    rw [Real.sq_sqrt]
    linarith

  have h3 : (Real.sqrt x + Real.sqrt 3) ^ 2 = Real.sqrt x ^ 2 + 2 * (Real.sqrt x * Real.sqrt 3) + Real.sqrt 3 ^ 2 := by 
    ring
  
  have h4 : Real.sqrt x ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith
  
  have h5 : Real.sqrt 3 ^ 2 = 3 := by 
    rw [Real.sq_sqrt]
    all_goals norm_num
  
  have h6 : Real.sqrt (x + 7) ^ 2 = (Real.sqrt x + Real.sqrt 3) ^ 2 := by
    rw [h1]
  
  rw [h2, h3] at h6
  rw [h4, h5] at h6
  
  have h7 : 7 = 2 * (Real.sqrt x * Real.sqrt 3) + 3 := by 
    nlinarith
  
  have h8 : 4 = 2 * (Real.sqrt x * Real.sqrt 3) := by 
    linarith
  
  have h9 : 2 = Real.sqrt x * Real.sqrt 3 := by 
    linarith
  
  have h10 : (Real.sqrt x * Real.sqrt 3) ^ 2 = 4 := by 
    calc
      (Real.sqrt x * Real.sqrt 3) ^ 2 = (2) ^ 2 := by rw [h9]
      _ = 4 := by norm_num
  
  have h11 : (Real.sqrt x * Real.sqrt 3) ^ 2 = (Real.sqrt x) ^ 2 * (Real.sqrt 3) ^ 2 := by 
    ring_nf
  
  have h12 : (Real.sqrt x) ^ 2 * (Real.sqrt 3) ^ 2 = x * 3 := by 
    rw [h4, h5]
    all_goals linarith
  
  have h13 : x * 3 = 4 := by 
    nlinarith [h10, h11, h12]
  
  linarith