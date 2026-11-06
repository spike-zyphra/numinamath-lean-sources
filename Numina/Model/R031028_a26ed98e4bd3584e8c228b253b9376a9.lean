import Mathlib

theorem other_6954 :
  Nat.digits 8 (Nat.ofDigits 2 [1, 0, 1, 1, 0, 1, 1, 0, 1]) = [5, 5, 5] ∧ Nat.digits 8 (Nat.ofDigits 2 [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1]) = [1, 5, 1, 3, 5] := by
  constructor
  · -- Convert the first binary number
    native_decide
  · -- Convert the second binary number
    native_decide