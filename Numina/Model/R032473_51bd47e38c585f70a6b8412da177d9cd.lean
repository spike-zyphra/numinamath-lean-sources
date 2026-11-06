import Mathlib

theorem number_theory_218781 : 
    ((Nat.digits 10 (4^(5^6) + 6^(5^4))).takeWhile (· = 0)).length = 5 := by 
  native_decide