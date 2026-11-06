import Mathlib

theorem number_theory_191162 : (∑ i ∈ Finset.Icc 1 2018, i^3) % 10 = 1 := by 
  native_decide