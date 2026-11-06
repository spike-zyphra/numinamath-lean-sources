import Mathlib

theorem number_theory_13058 : (Nat.digits 7 (Nat.ofDigits 7 [4, 2] * Nat.ofDigits 7 [0, 3])).sum = 6 := by 
  norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]