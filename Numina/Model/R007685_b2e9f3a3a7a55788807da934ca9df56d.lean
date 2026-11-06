import Mathlib

theorem number_theory_15219 : Nat.gcd (2^1001 - 1) (2^1012 - 1) = 2047 := by
  norm_num [Nat.gcd]