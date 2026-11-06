import Mathlib

theorem number_theory_60649 : (∏ i ∈ Finset.Icc 1 42, (i ^ 2 + 1)) % 43 = 4 := by 
  native_decide