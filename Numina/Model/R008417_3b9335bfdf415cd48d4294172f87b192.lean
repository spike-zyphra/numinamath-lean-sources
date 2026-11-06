import Mathlib

theorem number_theory_23194 : (Nat.ofDigits 3 [1, 2, 1, 2]) - (Nat.ofDigits 3 [2, 1, 2]) = (Nat.ofDigits 3 [2, 0, 2, 1]) := by
  norm_num [Nat.ofDigits]