import Mathlib

theorem number_theory_12228 : (∑ k in Finset.range 202, (10 * k + 7) ^ (k + 1)) % 10 = 6 := by
  native_decide