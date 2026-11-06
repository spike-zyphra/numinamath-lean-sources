import Mathlib

theorem algebra_95580 : (Nat.factorial 11 - Nat.factorial 10) / Nat.factorial 9 = 100 := by 
  norm_num [Nat.factorial]