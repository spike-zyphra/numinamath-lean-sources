import Mathlib

theorem number_theory_304076 : (Nat.divisors 1984).card = 14 ∧ ∑ x in (Nat.divisors 1984), x = 4064 := by 
  constructor
  · -- Show that the number of divisors is 14
    native_decide
  · -- Show that the sum of all divisors is 4064
    native_decide