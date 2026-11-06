import Mathlib

theorem number_theory_14721 : (Nat.digits 5 (Nat.ofDigits 8 [7, 2, 4])).length = 4 ∧
    (Nat.digits 5 (Nat.ofDigits 8 [7, 2, 4])) = [4, 0, 1, 2] := by 
  constructor
  · native_decide
  · native_decide