import Mathlib

open Real

theorem algebra_152393 : ∑ i ∈ Finset.range 1008, ((i + 1)^2 + (i + 2)^2) / ((i + 1) * (i + 2)) = 2016 + 1008 / 1009 := by
  native_decide