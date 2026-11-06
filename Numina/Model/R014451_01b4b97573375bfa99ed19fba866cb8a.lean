import Mathlib

theorem number_theory_207548 : (∑ i ∈ Finset.range 2015, ⌊(2 ^ i / 3 : ℝ)⌋) % 100 = 15 := by
  norm_num [Finset.sum_range_succ]