import Mathlib

/- What is the positive difference between the sum of the first 20 positive even integers and the sum of the first 15 positive odd integers? -/
theorem algebra_11769 : (∑ i in Finset.range 20, (2 * i + 2)) - (∑ i in Finset.range 15, (2 * i + 1)) = 195 := by
  simp [Finset.sum_range_succ]
  <;> rfl