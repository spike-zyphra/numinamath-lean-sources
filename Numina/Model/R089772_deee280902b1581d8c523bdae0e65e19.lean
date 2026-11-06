import Mathlib

theorem number_theory_6264 : (Nat.digits 10 ((Nat.ofDigits 10 (List.replicate 2021 9)) * (Nat.ofDigits 10 (List.replicate 2021 7)))).sum = 18189 := by
  native_decide