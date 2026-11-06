import Mathlib

theorem number_theory_143802 : ∑ i ∈ Finset.range 68, ⌊(17 * (i + 1))/(23 : ℝ)⌋ = 1701 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]