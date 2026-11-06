import Mathlib

def f (m : ℕ) := (m % 10)

def a (n : ℕ) := f (2 ^ (n + 1) - 1)

theorem number_theory_220231 : a 1994 = 7 := by
  unfold a f 
  norm_num