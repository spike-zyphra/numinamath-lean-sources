import Mathlib

def f (a b : ℤ) := 3 * a + 4 * b - a * b

theorem algebra_16430 : f 5 2 = 13 := by
  unfold f
  norm_num