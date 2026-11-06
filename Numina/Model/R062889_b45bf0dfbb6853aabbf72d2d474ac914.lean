import Mathlib

theorem algebra_18959 (x : ℝ) (hx : 0 < x) (h : Real.logb 2 x + Real.logb 2 (x ^ 2) = 6) :
    x = 4 := by
  have h1 : Real.logb 2 (x ^ 2) = 2 * Real.logb 2 x := by 
    simp [Real.logb_pow]
  rw [h1] at h 
  have h2 : 3 * Real.logb 2 x = 6 := by 
    linarith 
  have h3 : Real.logb 2 x = 2 := by 
    linarith 
  have h4 : x = (2 : ℝ) ^ (Real.logb 2 x) := by 
    rw [Real.rpow_logb]
    all_goals linarith 
  rw [h3] at h4 
  have hx_eq : x = (2 : ℝ) ^ (2 : ℝ) := by 
    linarith 
  norm_num at hx_eq ⊢
  linarith