import Mathlib

theorem number_theory_10003 : (∏ i ∈ Finset.range 167, (7 + 12 * i)) % 100 = 75 := by
  native_decide