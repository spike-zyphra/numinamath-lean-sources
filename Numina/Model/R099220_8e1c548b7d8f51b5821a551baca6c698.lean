import Mathlib

theorem number_theory_190201 : (Nat.primeFactors 27000001).card = 4 ∧ ∑ p ∈ (Nat.primeFactors 27000001), p = 652 := by 
  native_decide