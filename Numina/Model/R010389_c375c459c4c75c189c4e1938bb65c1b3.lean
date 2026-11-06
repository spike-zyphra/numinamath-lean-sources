import Mathlib

theorem number_theory_13182 : (Nat.primeFactors (∑ d in (400 : ℕ).divisors, d)).card = 1 := by 
  native_decide