import Mathlib

theorem algebra_12777 : ∑ i ∈ Finset.range 10, (-1 : ℤ) ^ (i + 1) * 2 ^ i = 341 := by
  norm_num [Finset.sum_range_succ]