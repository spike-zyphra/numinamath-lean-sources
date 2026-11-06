import Mathlib

theorem number_theory_175916 : (Nat.digits 10 ((Nat.ofDigits 10 (List.replicate 2014 9)) * (Nat.ofDigits 10 (List.replicate 2014 4)))).sum = 18126 := by
  native_decide