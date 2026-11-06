import Mathlib

theorem number_theory_23173 : Nat.ofDigits 2 [1] + Nat.ofDigits 2 [1, 1] + Nat.ofDigits 2 [1, 1, 1] + Nat.ofDigits 2 [1, 1, 1, 1] = Nat.ofDigits 2 [0, 1, 0, 1, 1] := by
  rfl