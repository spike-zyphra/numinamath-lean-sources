import Mathlib

theorem number_theory_192443 : (∏ i ∈ Finset.range 1003, (2 * i + 1)) % 1000 = 375 := by
  native_decide