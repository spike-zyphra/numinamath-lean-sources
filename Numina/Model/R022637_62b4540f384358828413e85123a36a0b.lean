import Mathlib

theorem number_theory_101390 : (∏ i ∈ Finset.Icc 1 2011, (2^i + 1)) % 100 = 75 := by 
  native_decide