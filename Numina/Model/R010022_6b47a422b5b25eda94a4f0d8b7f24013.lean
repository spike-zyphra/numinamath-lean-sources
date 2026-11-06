import Mathlib

theorem number_theory_12780 : Nat.digits 3 (25 + 36) = [1, 2, 0, 2] := by 
  norm_num [Nat.digits, Nat.digitsAux]