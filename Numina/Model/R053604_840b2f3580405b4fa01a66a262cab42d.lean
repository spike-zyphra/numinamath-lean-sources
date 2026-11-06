import Mathlib

theorem number_theory_206525 : (Nat.digits 10 (Nat.ofDigits 10 (List.replicate 2012 4) * Nat.ofDigits 10 (List.replicate 2012 9))).sum = 18108 := by
  native_decide