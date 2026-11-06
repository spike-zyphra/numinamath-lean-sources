import Mathlib

def f (x y : ℤ) := (x + y) * (x - y) 

theorem algebra_10519 : f 6 3 = 27 := by
  unfold f
  norm_num