import Mathlib

theorem algebra_846 {a b c : ℝ} (h1 : a + b + c = 3) (h2 : a^2 + b^2 + c^2 = 3) :
    a^2005 + b^2005 + c^2005 = 3 := by
  have h3 : (a - 1)^2 + (b - 1)^2 + (c - 1)^2 = 0 := by
    nlinarith
  
  have ha1 : (a - 1)^2 = 0 := by 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have hb1 : (b - 1)^2 = 0 := by 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have hc1 : (c - 1)^2 = 0 := by 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have ha : a = 1 := by
    nlinarith
  
  have hb : b = 1 := by 
    nlinarith
  
  have hc : c = 1 := by
    nlinarith
  
  rw [ha, hb, hc]
  norm_num