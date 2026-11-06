import Mathlib

theorem algebra_17257 (n : ℤ) (h : ∑ i ∈ Finset.range 49, (n + i) = 7^5) :
    (n + 24) = 343 := by
  norm_num [Finset.sum_range_succ] at h
  linarith