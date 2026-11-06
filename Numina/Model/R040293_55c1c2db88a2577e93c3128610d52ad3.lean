import Mathlib

theorem number_theory_23395 : (Nat.ofDigits 64 [0, 0, 1]) = Nat.ofDigits 62 [4, 4, 1] := by
  norm_num [Nat.ofDigits]