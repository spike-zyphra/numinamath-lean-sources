import Mathlib

theorem algebra_3986 : ∑ i ∈ Finset.range 80, (1 / (i * 4 + 4)) + (1 / (i * 12 + 12)) + (1 / (i * 24 + 24)) = 99 / 200 := by
  norm_num [Finset.sum_range_succ]