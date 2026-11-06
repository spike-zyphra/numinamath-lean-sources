import Mathlib

theorem number_theory_23059 : (∑ i ∈ Finset.range 101, 2^i) % 7 = 3 := by 
  native_decide