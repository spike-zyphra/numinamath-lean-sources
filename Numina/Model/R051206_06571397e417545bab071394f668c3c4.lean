import Mathlib

theorem number_theory_284166 : (∑ i ∈ Finset.range 2005, 2005^(i + 1)) % 100 = 5 := by 
  native_decide