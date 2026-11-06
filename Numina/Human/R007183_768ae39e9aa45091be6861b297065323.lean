import Mathlib

theorem number_theory_233111 : (Nat.digits 10 (1990^2003)).length = (Nat.digits 10 (1990^2003 + 2^2003)).length := by 
  native_decide