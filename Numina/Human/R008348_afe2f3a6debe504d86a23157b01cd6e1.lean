import Mathlib

/- Sum $324_8$ and $111010101110_2$, expressing your answer in base 8. -/
theorem number_theory_23005 : (Nat.ofDigits 8 [4, 2, 3]) + (Nat.ofDigits 2 [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1]) = Nat.ofDigits 8 [2, 0, 6, 7] := by
  dsimp [Nat.ofDigits]