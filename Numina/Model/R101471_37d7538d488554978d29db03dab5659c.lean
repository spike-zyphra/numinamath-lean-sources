import Mathlib

theorem number_theory_217254 :
    ∃ x y : ℕ, x < y ∧ (x.divisors.card = y.divisors.card) ∧
      ∑ d ∈ x.divisors, d > ∑ d ∈ y.divisors, d := by 
  use 34, 35
  constructor
  · norm_num
  constructor
  · native_decide
  · native_decide