import Mathlib

def sum_of_proper_divisors (n : ℕ) : ℕ := ∑ d in n.properDivisors, d

theorem number_theory_3589 : sum_of_proper_divisors (sum_of_proper_divisors (sum_of_proper_divisors (sum_of_proper_divisors (sum_of_proper_divisors 32 + 1) + 1) + 1) + 1) = 31 := by 
  native_decide