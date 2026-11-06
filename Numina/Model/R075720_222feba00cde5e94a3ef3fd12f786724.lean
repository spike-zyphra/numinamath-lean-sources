import Mathlib

theorem algebra_93961 : ∑ i ∈ Finset.range 99, (-1 : ℚ)^i * (i + 1) = 50 := by
  norm_num [Finset.sum_range_succ]