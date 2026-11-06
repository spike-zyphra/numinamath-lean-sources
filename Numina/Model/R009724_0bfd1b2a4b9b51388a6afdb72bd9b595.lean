import Mathlib

theorem number_theory_14395 : Nat.ofDigits 6 [0, 1, 2, 3, 4] - Nat.ofDigits 7 [0, 1, 2, 3] = 4776 := by
  norm_num [Nat.ofDigits]