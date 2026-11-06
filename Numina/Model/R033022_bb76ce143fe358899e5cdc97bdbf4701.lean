import Mathlib

theorem number_theory_15615 : (Nat.ofDigits 5 [1, 2, 1, 1]) / (Nat.ofDigits 5 [2, 1]) =
    Nat.ofDigits 5 [3, 4] := by
  norm_num [Nat.ofDigits]