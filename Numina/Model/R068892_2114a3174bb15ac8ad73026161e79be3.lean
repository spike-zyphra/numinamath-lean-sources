import Mathlib

theorem number_theory_23369 : (Nat.ofDigits 7 [1, 2, 3]) - (Nat.ofDigits 5 [1, 2, 3]) = 76 := by
  norm_num [Nat.ofDigits]