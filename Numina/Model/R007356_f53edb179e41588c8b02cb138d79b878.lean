import Mathlib

theorem number_theory_13198 : (Nat.ofDigits 2 [1, 1, 0, 1] : ℤ) + Nat.ofDigits 2 [1, 0, 1] -
    Nat.ofDigits 2 [0, 0, 1, 1] + Nat.ofDigits 2 [1, 0, 1, 1] =
    Nat.ofDigits 2 [1, 0, 0, 0, 1] := by 
  rfl