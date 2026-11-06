import Mathlib

theorem number_theory_120798 : (∑ i ∈ Finset.Icc 1 1992, i ^ i) % 10 = 0 := by
  native_decide