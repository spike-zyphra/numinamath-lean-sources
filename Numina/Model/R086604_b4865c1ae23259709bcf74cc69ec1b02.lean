import Mathlib

theorem algebra_225540 : ⌊(∑ i ∈ Finset.range 10, (0.81 + 0.02 * i) * 0.6 : ℝ)⌋ = 5 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]