import Mathlib

def f (x y : ℝ) := x ^ 2 + x * y - y ^ 2

theorem algebra_11663 : f 3 2 = 11 := by
  norm_num [f]