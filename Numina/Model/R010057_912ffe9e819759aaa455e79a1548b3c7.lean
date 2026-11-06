import Mathlib

theorem number_theory_15429 : Nat.ofDigits 11 [9, 4, 2] + Nat.ofDigits 12 [11, 10, 3] =
    Nat.ofDigits 10 [8, 5, 8] := by
  norm_num [Nat.ofDigits]