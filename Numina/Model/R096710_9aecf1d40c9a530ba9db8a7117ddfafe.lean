import Mathlib

theorem algebra_2948 : ∑ i in Finset.range 10, (3 * i + 1) * (3 * i + 3) * (3 * i + 5) = 81015 := by
  norm_num [Finset.sum_range_succ]