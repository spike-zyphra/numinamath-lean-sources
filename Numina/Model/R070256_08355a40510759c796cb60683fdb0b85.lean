import Mathlib

theorem number_theory_151210 : (Nat.digits 10 ((Nat.digits 10 (Nat.digits 10 (2012 ^ 2012)).sum).sum)).sum = 7 := by
  native_decide