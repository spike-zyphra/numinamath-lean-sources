import Mathlib

theorem algebra_13843 (u v : ℝ) (h₁ : (9 * 54 + u + v) / 11 = 66) :
    (u + v) / 2 = 120 := by 
  have h2 : 9 * 54 + u + v = 66 * 11 := by 
    linarith
  
  have h3 : u + v = 240 := by 
    linarith
  
  calc 
    (u + v) / 2 = 240 / 2 := by rw [h3]
    _ = 120 := by norm_num