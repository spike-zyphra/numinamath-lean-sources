import Mathlib

theorem number_theory_98943 : (∑ i ∈ Finset.range 2012, 3^(i+1)) % 100 = 60 := by
  native_decide