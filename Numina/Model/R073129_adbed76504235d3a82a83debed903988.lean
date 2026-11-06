import Mathlib

theorem algebra_270579 : ∑ i ∈ Finset.range 1001, (-1 : ℚ)^i * (2 * i + 1) = 1001 := by
  norm_num [Finset.sum_range_succ]