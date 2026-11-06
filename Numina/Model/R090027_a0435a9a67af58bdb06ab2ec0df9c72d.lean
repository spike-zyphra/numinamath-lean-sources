import Mathlib

theorem number_theory_10023 : (Nat.primeFactors 999973).card = 3 ∧ ∑ x ∈ Nat.primeFactors 999973, x = 171 := by
  constructor
  · -- Show the cardinality of the set of prime factors is 3
    native_decide
  · -- Show the sum of the prime factors equals 171
    native_decide