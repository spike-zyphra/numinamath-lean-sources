import Mathlib

/- What is the sum of all the odd integers between $300$ and $500$? -/
theorem algebra_11646 : ∑ x in (Finset.Ioo 300 500).filter Odd, x = 40000 := by
  rfl