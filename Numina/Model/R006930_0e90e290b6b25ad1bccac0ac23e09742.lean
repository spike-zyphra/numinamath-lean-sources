import Mathlib
open Real

theorem algebra_94877 {x : ℝ} (h : (x - 10) * (10 / 100) = (x - 20) * (20 / 100)) :
x = 30 := by 
  linarith