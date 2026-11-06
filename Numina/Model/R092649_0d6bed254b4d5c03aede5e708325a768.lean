import Mathlib

theorem number_theory_161699 : (Nat.digits 10 (Nat.ofDigits 10 (List.replicate 100 1) + Nat.ofDigits 10 (List.replicate 50 2) + Nat.ofDigits 10 (List.replicate 25 4) + 2010)).sum = 303 := by 
  native_decide