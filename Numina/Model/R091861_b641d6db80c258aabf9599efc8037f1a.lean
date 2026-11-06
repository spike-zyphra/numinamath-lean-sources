import Mathlib

theorem number_theory_66133 : (∑ d in (Nat.divisors 2008), Nat.totient d) % 1000 = 8 := by 
  native_decide