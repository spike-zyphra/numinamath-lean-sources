import Mathlib

def roundness (n : ℕ) := ∑ p in Nat.primeFactors n, n.factorization p

theorem number_theory_145 : roundness 1000000 = 12 := by
  native_decide