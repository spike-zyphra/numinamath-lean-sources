import Mathlib

theorem number_theory_15404 : (Nat.ofDigits 6 [3, 4, 3, 2]) + (Nat.ofDigits 6 [5, 2, 3, 5, 1]) = Nat.ofDigits 6 [2, 1, 1, 2, 2] := by 
  norm_num [Nat.ofDigits]