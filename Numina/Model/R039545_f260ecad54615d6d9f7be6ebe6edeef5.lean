import Mathlib

theorem number_theory_322590 : ∑ k in Finset.range 2014, ⌊((2013 + 2^k : ℝ) / 2^(k + 1))⌋ = 2013 := by
  norm_num [Finset.sum_range_succ]
  <;> try { native_decide }