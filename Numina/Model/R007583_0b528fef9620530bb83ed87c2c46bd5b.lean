import Mathlib

theorem number_theory_14090 : (Nat.digits 2 (Nat.ofDigits 16 [6, 6, 6, 6, 6])).length = 19 := by
  native_decide