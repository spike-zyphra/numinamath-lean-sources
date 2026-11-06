import Mathlib

theorem number_theory_19583 : (Nat.ofDigits 11 [1, 1, 9, 2]) - (Nat.ofDigits 11 [2, 9, 3, 1]) = Nat.ofDigits 11 [10, 2, 5, 1] := by
  norm_num [Nat.ofDigits]