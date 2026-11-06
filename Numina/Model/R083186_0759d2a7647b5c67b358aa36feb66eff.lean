import Mathlib

theorem number_theory_233658 : (∑ i ∈ Finset.range 2017, (i + 1)^(i + 1)) % 10 = 1 := by
  native_decide