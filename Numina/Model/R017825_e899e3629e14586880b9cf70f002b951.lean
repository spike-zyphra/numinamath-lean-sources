import Mathlib

theorem algebra_323424 : 4 * (∑ i in Finset.range 1000, (-1 : ℚ) ^ (i + 1) * (i + 1)) = 2000 := by 
  native_decide