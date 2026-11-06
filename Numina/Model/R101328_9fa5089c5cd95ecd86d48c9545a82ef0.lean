import Mathlib

theorem algebra_274955 (x : ℤ) (h : 1 + 2 + 3 + 4 + 5 + x = ∑ i ∈ Finset.range 5, (21 + i)) :
    x = 100 := by
  norm_num [Finset.sum_range_succ] at h
  linarith