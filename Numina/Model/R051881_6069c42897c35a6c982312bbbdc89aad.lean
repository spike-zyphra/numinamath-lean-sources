import Mathlib

theorem algebra_264005 (n : ℝ) (h : Real.sqrt (5 + n) = 7) : n = 44 := by
  have h1 : (Real.sqrt (5 + n)) ^ 2 = (7 : ℝ) ^ 2 := by 
    rw [h]
    all_goals nlinarith
  have h2 : (Real.sqrt (5 + n)) ^ 2 = 5 + n := by 
    apply Real.sq_sqrt 
    by_contra h3
    push_neg at h3
    have h4 : Real.sqrt (5 + n) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals nlinarith
    rw [h4] at h 
    all_goals nlinarith
  have h3 : (7 : ℝ) ^ 2 = 49 := by norm_num
  rw [h2] at h1 
  nlinarith [show (7 : ℝ) ^ 2 = 49 by norm_num]