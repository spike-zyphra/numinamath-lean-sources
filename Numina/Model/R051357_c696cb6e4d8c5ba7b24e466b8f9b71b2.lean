import Mathlib

def f (x : ℝ) := 7 - x

def g (x : ℝ) := x - 7

theorem algebra_10521 : g (f 12) = -12 := by
  norm_num [f, g]