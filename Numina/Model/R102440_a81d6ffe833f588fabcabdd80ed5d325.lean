import Mathlib

theorem algebra_323603 (n : ℕ) (h : n > 0) (h' : ∑ i ∈ Finset.range 6, (n + i) = 2013) :
    n + 5 = 338 := by
  norm_num [Finset.sum_range_succ] at h'
  omega