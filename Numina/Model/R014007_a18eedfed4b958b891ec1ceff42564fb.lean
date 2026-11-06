import Mathlib

theorem number_theory_321049 : (∑ i in Finset.range 2010, ⌊(6^(i + 1))/(7 : ℝ)⌋) % 35 = 20 := by
  norm_num [Finset.sum_range_succ]