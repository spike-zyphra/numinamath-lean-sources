import Mathlib

theorem number_theory_22787 : (∑ i in Finset.range 100, (2 * i + 1)) % 7 = 4 := by
  native_decide