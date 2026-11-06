import Mathlib

theorem algebra_10677 : ∑ i ∈ Finset.range 10, (2^(i+1) : ℚ) / 3^(i+1) = 116050 / 59049 := by
  norm_num [Finset.sum_range_succ]