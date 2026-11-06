import Mathlib

theorem number_theory_14633 : (∑ i ∈ Finset.range 2005, 7^i) % 1000 = 801 := by
  native_decide