import Mathlib

theorem number_theory_28530 : ¬ Nat.Prime (∑ i ∈ Finset.range 1991, 10 ^ i) := by 
  native_decide