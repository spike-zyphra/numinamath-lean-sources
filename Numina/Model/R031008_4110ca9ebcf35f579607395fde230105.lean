import Mathlib

open Real

theorem inequalities_207339 : ∑ i ∈ Finset.range 201, ((1 / 2 : ℝ) ^ (200 - i)) * (1 / (i + 1)) < 1 / 90 := by
  norm_num [Finset.sum_range_succ]
  <;> norm_num
  <;> linarith