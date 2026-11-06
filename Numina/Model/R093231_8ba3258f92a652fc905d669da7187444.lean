import Mathlib

open Real

theorem calculus_54829 : ∑ i ∈ Finset.range 1996, (1 / (∑ j ∈ Finset.range (i + 1), (1 / (j + 1) * (j + 2) / 2))) > 1001 := by
  native_decide