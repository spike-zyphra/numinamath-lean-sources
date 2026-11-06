import Mathlib

def f (x y : ℝ) := x * y - (x + y) 

theorem algebra_283972 : f 6 (f 5 4) = 49 := by 
  dsimp [f]
  norm_num