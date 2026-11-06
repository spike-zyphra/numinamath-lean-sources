import Mathlib

def n : ℕ := 1993^3

theorem number_theory_1505 : (n % 7 = 6) := by
  norm_num [n]