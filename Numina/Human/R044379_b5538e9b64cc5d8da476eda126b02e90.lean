import Mathlib

/-Add $1_2 + 11_2 + 111_2 + 1111_2.$ Express your answer in base 2.-/
theorem number_theory_23173 : Nat.ofDigits 2 [1] + Nat.ofDigits 2 [1, 1] + Nat.ofDigits 2 [1, 1, 1] + Nat.ofDigits 2 [1, 1, 1, 1] = Nat.ofDigits 2 [0, 1, 0, 1, 1] := by
  simp [Nat.ofDigits]