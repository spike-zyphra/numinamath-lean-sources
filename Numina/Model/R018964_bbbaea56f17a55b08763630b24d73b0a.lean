import Mathlib

def a (i j : ℕ) : ℕ := match i with
  | 0 => 0
  | 1 => j ^ j
  | n + 2 => a (n + 1) j + a (n + 1) (j + 1)

theorem number_theory_165423 : a 128 1 % 10 = 4 := by
  norm_num [a]