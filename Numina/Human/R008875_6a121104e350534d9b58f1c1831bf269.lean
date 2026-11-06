import Mathlib

theorem number_theory_15489 : (Nat.digits 6 515) = [5, 1, 2, 2] := by 
  simp [Nat.digits, Nat.digitsAux]