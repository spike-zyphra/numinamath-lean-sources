import Mathlib

theorem number_theory_14439 : Nat.ofDigits 8 [5, 2, 3] - Nat.ofDigits 8 [7, 3, 2] =
    Nat.ofDigits 8 [6, 6] := by
  norm_num [Nat.ofDigits]