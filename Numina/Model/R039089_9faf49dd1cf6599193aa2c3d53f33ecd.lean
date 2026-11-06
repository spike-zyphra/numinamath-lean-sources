import Mathlib

theorem calculus_39659 : ∑ i ∈ Finset.range 2020, ((-1 : ℤ)^i : ℝ) / (i + 1) = ∑ i ∈ Finset.range 1010, (1 : ℝ) / (1011 + i) := by
  norm_num
  all_goals norm_num