import Mathlib

def g (x : ℝ) := 3 * x + 7
def f (x : ℝ) := 5 * x - 9

theorem algebra_13735 : f (g 8) = 146 := by 
  norm_num [f, g]