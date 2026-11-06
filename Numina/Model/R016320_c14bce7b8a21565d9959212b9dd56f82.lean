import Mathlib

theorem number_theory_311180 : (∑ k in Finset.Icc 0 201, (10 * k + 7) ^ (k + 1)) % 10 = 6 := by
  native_decide