import Mathlib

theorem number_theory_197029 : (∑ i in Finset.range 15, (∏ j in Finset.range (i + 1), (j + 1))) % 72 = 9 := by
  native_decide