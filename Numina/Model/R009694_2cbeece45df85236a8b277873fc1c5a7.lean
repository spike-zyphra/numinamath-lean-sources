import Mathlib

theorem number_theory_13108 : (Nat.ofDigits 6 [5, 5, 5]) + (Nat.ofDigits 6 [5, 5]) + (Nat.ofDigits 6 [5]) = Nat.ofDigits 6 [3, 0, 1, 1] := by 
  simp [Nat.ofDigits]
  <;> all_goals omega