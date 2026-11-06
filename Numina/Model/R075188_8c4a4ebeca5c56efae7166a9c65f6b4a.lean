import Mathlib

def f (x : ℝ) := 7 - x

def g (x : ℝ) := x - 7

theorem algebra_21427 : g (f 15) = -15 := by
  norm_num [f, g]