import Mathlib
theorem algebra_611067 : ∑ i in Finset.range 2001, ((-1 : ℝ) ^ i * (i + 1) * (i + 2)) = 2004002:= by
  norm_num [Finset.sum_range_succ]