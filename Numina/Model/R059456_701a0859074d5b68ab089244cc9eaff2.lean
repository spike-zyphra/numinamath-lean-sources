import Mathlib

theorem algebra_110285 : ∑ i in Finset.range 1010, (2 * i + 2)^2 - ∑ i in Finset.range 1010, (2 * i + 1)^2 = 2041210 := by
  native_decide