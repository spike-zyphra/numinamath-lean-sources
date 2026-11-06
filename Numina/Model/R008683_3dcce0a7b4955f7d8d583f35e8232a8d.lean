import Mathlib

theorem number_theory_15875 : Nat.ofDigits 8 [5, 3] - Nat.ofDigits 8 [4, 7] = -Nat.ofDigits 8 [7, 3] := by
  norm_num [Nat.ofDigits]