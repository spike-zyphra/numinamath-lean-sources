import Mathlib

theorem number_theory_4678 : ∑ p in (Nat.primeFactors ((3^8 + 3^7 + 1) : ℕ)), p = 686 := by
  native_decide