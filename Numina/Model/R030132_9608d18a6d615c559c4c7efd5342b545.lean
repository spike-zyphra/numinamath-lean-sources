import Mathlib
theorem algebra_609732 : ∑ i in Finset.range 25, (((4 * i + 4) ^ 2 : ℝ) + (4 * i + 3) ^ 2 - (4 * i + 2) ^ 2 - (4 * i + 1) ^ 2) = 10100:= by
  norm_num [Finset.sum_range_succ]