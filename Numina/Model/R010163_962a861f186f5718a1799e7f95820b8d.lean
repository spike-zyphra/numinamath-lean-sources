import Mathlib

theorem number_theory_12903 : Nat.ofDigits 9 [3, 1, 8] = Nat.ofDigits 3 [0, 1, 1, 0, 2, 2] := by 
  norm_num [Nat.ofDigits]