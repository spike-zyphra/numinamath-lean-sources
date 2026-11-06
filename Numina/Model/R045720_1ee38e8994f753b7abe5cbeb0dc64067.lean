import Mathlib

theorem number_theory_311820 : ∑ k in Finset.range 2020, ⌊(4^k / 5 : ℝ)⌋ = (4^2020 - 1) / 15 - 1010 := by 
  norm_num [Finset.sum_range_succ]