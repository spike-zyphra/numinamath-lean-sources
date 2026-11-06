import Mathlib

theorem number_theory_15398 : (Nat.digits 9 (Nat.ofDigits 9 [5, 7, 1] + Nat.ofDigits 9 [4, 1, 7] + Nat.ofDigits 9 [1, 6])) = [1, 6, 0, 1] := by 
  norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]