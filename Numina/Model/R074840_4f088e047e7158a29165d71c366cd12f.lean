import Mathlib

theorem number_theory_3319 : (∏ i in Finset.Icc 4 2015, i) % 2017 = 1681 := by 
  native_decide