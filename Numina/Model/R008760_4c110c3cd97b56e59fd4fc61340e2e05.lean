import Mathlib

theorem algebra_10365 : ∑ i ∈ Finset.range 6, (1 / 3^(i + 1) : ℚ) = 364 / 729 := by
  norm_num [Finset.sum_range_succ]