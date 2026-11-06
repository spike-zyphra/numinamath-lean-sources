import Mathlib

theorem number_theory_300460 : (Nat.floor (10^1988 * (10^989 - 1) / 999)) % 10 = 9 := by 
  norm_num [Nat.floor_eq_iff]