import Mathlib

theorem number_theory_156338 : (∑ i ∈ Finset.Icc 1 2021, 3^i) % 13 = 12 := by
  native_decide