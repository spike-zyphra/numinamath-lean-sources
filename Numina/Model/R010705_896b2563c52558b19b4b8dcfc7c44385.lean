import Mathlib

theorem number_theory_12072 : Nat.ofDigits 4 [3, 2, 0, 1] / Nat.ofDigits 4 [1, 1] =
    Nat.ofDigits 4 [3, 3] := by 
  simp [Nat.ofDigits]
  all_goals omega