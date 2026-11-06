import Mathlib

  theorem number_theory_19438 : (Nat.ofDigits 8 [6]) * (Nat.ofDigits 8 [7]) = Nat.ofDigits 8 [2, 5] := by
  norm_num [Nat.ofDigits]