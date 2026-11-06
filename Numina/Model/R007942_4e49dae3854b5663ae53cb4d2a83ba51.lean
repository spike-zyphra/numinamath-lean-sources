import Mathlib

theorem number_theory_23045 : (Nat.ofDigits 5 [3, 1, 4]) / (Nat.ofDigits 5 [2]) =
    Nat.ofDigits 5 [4, 0, 2] := by 
  norm_num [Nat.ofDigits]