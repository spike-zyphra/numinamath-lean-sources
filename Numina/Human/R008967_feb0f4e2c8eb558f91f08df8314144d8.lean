import Mathlib

/- What is the sum of the odd integers from 11 through 39, inclusive? -/
theorem algebra_10398 : ∑ i in (Finset.Icc 11 39).filter Odd, i = 375 := by 
  rfl