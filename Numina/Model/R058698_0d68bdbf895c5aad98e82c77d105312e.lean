import Mathlib

theorem number_theory_101257 : ∑ i ∈ Finset.Icc 1 1000, (Nat.digits 10 i).sum = 13501 := by
  native_decide