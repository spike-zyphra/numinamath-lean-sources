import Mathlib

theorem algebra_11114 : (∑ i in Finset.Icc 1 100, i^3) + (∑ i in Finset.Icc 1 100, (-i)^3) = 0 := by
  native_decide