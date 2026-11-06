import Mathlib

theorem number_theory_6347 : (Nat.digits 10 (Nat.ofDigits 10 (List.replicate 2020 9) * Nat.ofDigits 10 (List.replicate 2020 8))).sum = 18180 := by 
  native_decide