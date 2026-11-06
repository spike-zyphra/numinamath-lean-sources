import Mathlib

/- Compute $81_9 - 72_9$.  Express your answer in base 9. -/
theorem number_theory_19099 : (Nat.ofDigits 9 [1, 8] - Nat.ofDigits 9 [2, 7]) = Nat.ofDigits 9 [8] := by
  exact rfl