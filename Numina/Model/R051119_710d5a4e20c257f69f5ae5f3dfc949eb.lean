import Mathlib

theorem number_theory_14354 : gcd (Nat.factorial 5) (Nat.factorial 8 / Nat.factorial 3) = 120 := by
  norm_num [gcd, Nat.factorial]