import Mathlib

theorem number_theory_1532 : (∑ i ∈ Finset.range 23, (10 ^ (i + 1) - 1) * 3 / 9) % 10000 = 7029 := by
  norm_num [Finset.sum_range_succ]