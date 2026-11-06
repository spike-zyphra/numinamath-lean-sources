import Mathlib

open Real

theorem algebra_4560 : ∑ i ∈ Finset.range 1341, (1 / ((i + 1) * (i + 3))) = 1 / 1341 := by
  native_decide