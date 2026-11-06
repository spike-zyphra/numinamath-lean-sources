import Mathlib

theorem number_theory_129992 : ∑ k in Finset.range 2020, ⌊(4 ^ k : ℝ) / 5⌋ = (4 ^ 2020 - 1) / 15 - 1010 := by
  norm_num [Finset.sum_range_succ]