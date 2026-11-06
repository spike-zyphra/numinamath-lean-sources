import Mathlib

theorem number_theory_104986 : (∏ i in Finset.Icc 27 89, if Odd i then i else 1) % 10 = 5 := by
  native_decide