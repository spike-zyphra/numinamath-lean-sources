import Mathlib

def sol := (Nat.divisors 2125).card

theorem number_theory_4956 : sol = 8 := by
  native_decide