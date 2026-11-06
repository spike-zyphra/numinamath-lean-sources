import Mathlib

def a (n : ℕ) := 7 ^ n + 9 ^ n

theorem number_theory_320567 : a 2008 % 64 = 2 := by
  unfold a
  norm_num