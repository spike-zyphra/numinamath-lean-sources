import Mathlib

theorem number_theory_11066 : ((Nat.divisors (Nat.factorial 7)).filter Even).card  = 48 := by
  native_decide