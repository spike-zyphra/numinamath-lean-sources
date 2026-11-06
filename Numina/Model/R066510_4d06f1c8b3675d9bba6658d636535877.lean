import Mathlib

def is_abundant_number (n : ℕ) := ∑ d in n.divisors.erase n, d > n

theorem number_theory_278155 : is_abundant_number 18 := by
  unfold is_abundant_number
  native_decide