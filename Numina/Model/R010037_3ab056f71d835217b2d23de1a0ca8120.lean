import Mathlib

theorem number_theory_216728 : 
  (Nat.digits 10 ((10^112 - 1)^2))[72]! = 0 := by
  native_decide