import Mathlib

theorem number_theory_611311 : (Nat.primeFactors 27000001).card = 4 ∧
(Nat.primeFactors 27000001).sum id = 652 := by
  native_decide