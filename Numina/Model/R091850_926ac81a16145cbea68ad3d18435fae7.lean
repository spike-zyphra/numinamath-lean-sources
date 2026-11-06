import Mathlib

theorem number_theory_627 : (Nat.digits 10 ((∑ i ∈ Finset.range 2012, 10^i) ^ 2))[72]! = 0 := by
  native_decide