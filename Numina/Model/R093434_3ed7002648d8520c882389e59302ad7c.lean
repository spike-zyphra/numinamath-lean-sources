import Mathlib

theorem algebra_3821 : ∑ i ∈ Finset.range 99, (1 / (2 ^ (i + 1) + 2 ^ 50) : ℝ) = 99 / 2 ^ 51 := by
  norm_num [Finset.sum_range_succ]