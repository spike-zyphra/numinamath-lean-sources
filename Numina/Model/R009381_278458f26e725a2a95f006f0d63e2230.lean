import Mathlib

theorem algebra_13424 (x : ℝ) (hx : x > 0) (h : (1/2) * (2 * x) * (5 * x) + (2 * x) ^ 2 + (5 * x) ^ 2 = 850) :
    x = 5 := by 
  have eq1 : 34 * x^2 = 850 := by 
    nlinarith 
  have eq2 : x^2 = 25 := by
    nlinarith 
  have h1 : x = 5 := by 
    nlinarith [sq_pos_of_pos hx, eq2]
  linarith 
  all_goals nlinarith 
  all_goals nlinarith