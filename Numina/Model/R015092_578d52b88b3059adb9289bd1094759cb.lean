import Mathlib

theorem number_theory_217210 :
    ∃ x y : ℕ, x > y ∧ (x.divisors.card = y.divisors.card) ∧ (∑ d ∈ x.divisors, d < ∑ d ∈ y.divisors, d) := by
  use 45, 44
  constructor
  · -- Show that 45 > 44
    norm_num
  constructor
  · -- Show that 45 and 44 have the same number of divisors
    native_decide
  · -- Show that the sum of divisors of 45 is less than the sum of divisors of 44
    native_decide