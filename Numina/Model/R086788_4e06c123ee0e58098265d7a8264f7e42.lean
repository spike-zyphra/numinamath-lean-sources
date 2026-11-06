import Mathlib

theorem number_theory_6582 : (∑ i ∈ Finset.range 2020, (10 ^ (i + 1) - 1) / 9) % 100 = 10 := by
  native_decide