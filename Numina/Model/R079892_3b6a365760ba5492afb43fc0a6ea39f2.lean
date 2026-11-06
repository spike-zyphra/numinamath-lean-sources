import Mathlib

theorem number_theory_23408 : (∑ i ∈ Finset.Icc 2010 4018, i) % 2009 = 0 := by
  native_decide