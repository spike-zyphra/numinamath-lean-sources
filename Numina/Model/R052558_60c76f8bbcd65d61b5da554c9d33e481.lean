import Mathlib

theorem number_theory_13211 : ∃ p : ℕ, Nat.Prime p ∧ p ∈ Finset.Icc (10^17) (10^17 + 10) := by
  use 10^17 + 3
  constructor
  · -- Show 10^17 + 3 is prime
    native_decide
  · -- Show 10^17 + 3 is in the interval [10^17, 10^17 + 10]
    native_decide