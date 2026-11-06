import Mathlib

def sol := (Nat.divisors 2002).card

theorem number_theory_2775 : sol = 16 := by 
  native_decide