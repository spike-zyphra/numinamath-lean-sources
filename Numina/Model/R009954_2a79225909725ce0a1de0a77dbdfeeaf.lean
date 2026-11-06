import Mathlib

theorem algebra_609847: ∏ i ∈ Finset.range 1009, ((1:ℝ) + 1 / (2 * i + 2)) < 50 := by
  norm_num [Finset.prod_range_succ]
  <;> native_decide