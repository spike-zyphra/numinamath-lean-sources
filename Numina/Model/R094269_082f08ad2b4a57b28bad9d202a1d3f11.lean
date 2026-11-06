import Mathlib

theorem algebra_55026 : ∑ i in Finset.range 17, (i * 3 + 2) = 442 := by
  norm_num [Finset.sum_range_succ]