import Mathlib

theorem number_theory_614 : (∑ i in Finset.range 1991, 1991 * 10 ^ (i * 4)) % 13 = 8 := by
  native_decide