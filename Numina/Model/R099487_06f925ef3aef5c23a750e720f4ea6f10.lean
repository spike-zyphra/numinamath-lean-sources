import Mathlib

def f (a b : ℤ) := (a - b) / 3
def g (a b : ℤ) := (a + b) * 3

theorem algebra_132982 : g (f 39 12) 3 = 36 := by 
  unfold f g 
  norm_num