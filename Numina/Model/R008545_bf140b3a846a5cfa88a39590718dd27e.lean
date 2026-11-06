import Mathlib

theorem number_theory_15759 : (∑ i ∈ Finset.range 21, (i * 5 + 1)) % 15 = 6 := by
  native_decide