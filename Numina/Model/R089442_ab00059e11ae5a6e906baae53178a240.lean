import Mathlib

theorem algebra_3134 : ∑ i ∈ Finset.range 20, (2*i + 2) * (2*i + 4) = 12320 := by
  norm_num [Finset.sum_range_succ]