import Mathlib

open Real

theorem algebra_155896 : ∑ i ∈ Finset.range 2005, ((i + 1)^2 + (i + 2)^2) / ((i + 1) * (i + 2)) = 4010 + 2005 / 2006 := by
  native_decide