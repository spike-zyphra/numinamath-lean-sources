import Mathlib

theorem number_theory_16220 : (∑ i ∈ Finset.range 44, (i * 6 + 1)) % 6 = 2 := by
  norm_num [Finset.sum_range_succ]