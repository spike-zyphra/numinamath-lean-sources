import Mathlib

theorem number_theory_23400 : ∑ x in (Nat.divisors (Nat.sqrt 196)), x = 24 := by
  native_decide