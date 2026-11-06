import Mathlib

theorem algebra_4992 : ∑ i ∈ Finset.range 1007, (1 / ((2014 + i) * (2015 + i) + 1)) = 2011 / 8060 := by
  native_decide