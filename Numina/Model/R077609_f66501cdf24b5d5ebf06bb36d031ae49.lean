import Mathlib

def a : ℕ → ℕ → ℕ
| 0, n => n ^ n
| i + 1, j => a i j + a i (j + 1)

theorem number_theory_327121 : a 127 1 % 10 = 4 := by
  norm_num [a]