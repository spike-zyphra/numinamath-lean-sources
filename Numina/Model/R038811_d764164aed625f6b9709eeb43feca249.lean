import Mathlib

theorem number_theory_106001 : (∑ i ∈ Finset.range 2020, ⌊(19^(i+1))/(20 : ℝ)⌋) % 11 = 2 := by
  norm_num [Finset.sum_range_succ]