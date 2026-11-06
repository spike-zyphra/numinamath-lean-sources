import Mathlib

theorem number_theory_17146 : ∑ d in (Nat.divisors 180).filter Odd, d = 78 := by
  native_decide