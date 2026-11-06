import Mathlib

open Real

theorem algebra_13007 : ∑ i ∈ Finset.range 100, (2 + (i + 1) * 6 : ℚ) / 4^(100 - i) = 200 := by
  norm_num [Finset.sum_range_succ]
  <;> linarith