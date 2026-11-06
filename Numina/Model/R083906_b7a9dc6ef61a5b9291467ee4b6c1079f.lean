import Mathlib

def f (x y : ℤ) := (x + y) * (x - y)

theorem algebra_19946 : f 6 5 = 11 := by
  unfold f 
  norm_num