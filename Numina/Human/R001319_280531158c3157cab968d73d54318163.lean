import Mathlib

/-Find the units digit of the following within the indicated number base: $413_6 - 215_6$-/
theorem number_theory_23439 : (Nat.ofDigits 6 [3, 1, 4] - Nat.ofDigits 6 [5, 1, 2]) % 6 = 4 := by
  simp [Nat.ofDigits]