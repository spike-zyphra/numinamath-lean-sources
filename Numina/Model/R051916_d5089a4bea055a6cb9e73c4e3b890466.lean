import Mathlib

theorem number_theory_3380 : ((∑ i in Finset.range 2019, (i + 1)^2) + (∑ i in Finset.range 4037, (i + 1))) % 1013 = 14 := by 
  native_decide