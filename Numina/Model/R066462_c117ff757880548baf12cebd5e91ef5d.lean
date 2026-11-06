import Mathlib

theorem number_theory_304227 : (∑ i ∈ Finset.range 2016, ⌊(7^(i+1))/(8 : ℝ)⌋) % 50 = 42 := by
  norm_num [Finset.sum_range_succ]
  <;> native_decide