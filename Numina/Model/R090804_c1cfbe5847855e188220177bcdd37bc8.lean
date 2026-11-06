import Mathlib

theorem algebra_5230 {x y : ℝ} (h1 : (5*x-3*y)/9=10) (h2 : (2*x+5*y)/10=16) : y=20 := by
  have eq1 : 5 * x - 3 * y = 90 := by 
    linarith
  have eq2 : 2 * x + 5 * y = 160 := by 
    linarith
  have eq3 : 31 * x = 930 := by 
    linarith [eq1, eq2]
  have hx : x = 30 := by 
    linarith
  have hy : y = 20 := by 
    linarith [eq1, hx]
  exact hy