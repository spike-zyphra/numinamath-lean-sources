import Mathlib

theorem algebra_1136
  (a b c : ℝ ) (h1 : a ^ 2 + 2 * b  = 7) (h2 : b^2 + 4 * c = -7) (h3 : c^2 + 6 * a = -14) :
  (a^2 + b^2 + c^2 = 14) := by 
  have eq1 : a ^ 2 + b ^ 2 + c ^ 2 + 2 * b + 4 * c + 6 * a = -14 := by 
    nlinarith
  
  have eq2 : (a + 3) ^ 2 + (b + 1) ^ 2 + (c + 2) ^ 2 = 0 := by 
    nlinarith
  
  have ha : (a + 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 3), sq_nonneg (b + 1), sq_nonneg (c + 2)]
    
  have hb : (b + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 3), sq_nonneg (b + 1), sq_nonneg (c + 2)]
    
  have hc : (c + 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 3), sq_nonneg (b + 1), sq_nonneg (c + 2)]
  
  have ha2 : a + 3 = 0 := by
    rw [sq_eq_zero_iff] at ha 
    exact ha
  
  have hb2 : b + 1 = 0 := by
    rw [sq_eq_zero_iff] at hb 
    exact hb
  
  have hc2 : c + 2 = 0 := by
    rw [sq_eq_zero_iff] at hc 
    exact hc
  
  have ha3 : a = -3 := by 
    linarith
  
  have hb3 : b = -1 := by 
    linarith
  
  have hc3 : c = -2 := by 
    linarith
  
  rw [ha3, hb3, hc3]
  norm_num