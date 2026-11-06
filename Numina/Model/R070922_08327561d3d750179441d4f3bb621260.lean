import Mathlib

theorem number_theory_22735 : (∑ i in Finset.range 11, (-1 : ℤ)^i * (i + 1)) % 8 = 6 := by
  norm_num [Finset.sum_range_succ]