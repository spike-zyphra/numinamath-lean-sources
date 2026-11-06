import Mathlib

theorem number_theory_19495 : ∑ x in (Nat.divisors 6300).filter Odd, x = 3224 := by
  native_decide