import Mathlib

theorem algebra_21685 (n : ℕ) (hn : 0 < n) (h : ∑ i ∈ Finset.range 27, (n + i) = 3^7) :
    (n + 13) = 81 := by
  norm_num [Finset.sum_range_succ] at h
  omega