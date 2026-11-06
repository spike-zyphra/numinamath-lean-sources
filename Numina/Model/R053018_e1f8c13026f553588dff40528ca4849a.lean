import Mathlib

theorem algebra_254240 : ((Real.sqrt (1 + Real.sqrt (1 + Real.sqrt 1))) ^ 4 = 3 + 2 * Real.sqrt 2) := by
  have h1 : Real.sqrt 1 = 1 := by
    simp [Real.sqrt_eq_iff_sq_eq]
  
  have h2 : Real.sqrt (1 + Real.sqrt 1) = Real.sqrt 2 := by 
    rw [h1]
    norm_num
  
  have h3 : Real.sqrt (1 + Real.sqrt (1 + Real.sqrt 1)) = Real.sqrt (1 + Real.sqrt 2) := by 
    rw [h2]
  
  have h4 : ((Real.sqrt (1 + Real.sqrt (1 + Real.sqrt 1))) ^ 2) = 1 + Real.sqrt 2 := by 
    rw [h3]
    have h5 : (Real.sqrt (1 + Real.sqrt 2)) ^ 2 = 1 + Real.sqrt 2 := by 
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (1 + Real.sqrt 2)]
  
  calc
    (Real.sqrt (1 + Real.sqrt (1 + Real.sqrt 1))) ^ 4
        = ((Real.sqrt (1 + Real.sqrt (1 + Real.sqrt 1))) ^ 2) ^ 2 := by ring
    _ = (1 + Real.sqrt 2) ^ 2 := by rw [h4]
    _ = 3 + 2 * Real.sqrt 2 := by 
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]