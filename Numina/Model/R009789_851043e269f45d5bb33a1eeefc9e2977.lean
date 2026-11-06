import Mathlib

theorem number_theory_16048 : Nat.ofDigits 6 [4] + Nat.ofDigits 6 [4, 1] = Nat.ofDigits 6 [2, 2] := by
  simp [Nat.ofDigits]
  <;> try { omega }
  all_goals simp [Nat.ofDigits] <;> omega