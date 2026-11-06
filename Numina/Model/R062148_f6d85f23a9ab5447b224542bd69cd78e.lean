import Mathlib

theorem number_theory_247715 : (∑ i ∈ Finset.range 2013, 3^(i+1)) % 10 = 3 := by 
  native_decide