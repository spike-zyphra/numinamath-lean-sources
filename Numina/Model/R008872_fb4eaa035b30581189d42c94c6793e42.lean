import Mathlib

theorem number_theory_15485 : (∑ i in Finset.range 2010, (-1 : ℤ)^i * (i + 1)) % 2010 = 1005 := by 
  native_decide