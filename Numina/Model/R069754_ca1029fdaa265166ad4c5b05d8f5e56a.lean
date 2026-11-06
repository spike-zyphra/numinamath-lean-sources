import Mathlib

def f (n m : ℕ) := n * 10 + m
def g (n m : ℕ) := n * 10 ^ m + m

theorem algebra_193705 : f 2018 (g 123 4) = 1250184 := by
  norm_num [f, g]