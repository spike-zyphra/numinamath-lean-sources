import Mathlib

theorem number_theory_3553 : (∏ i ∈ Finset.range 1006, (2 * i + 1)) % 100 = 75 := by
  native_decide