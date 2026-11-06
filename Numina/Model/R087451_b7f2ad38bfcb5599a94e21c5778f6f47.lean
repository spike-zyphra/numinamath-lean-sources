import Mathlib

theorem algebra_146920 (n : ℕ) (h : ∑ i ∈ Finset.range 6, (n + 9 - i) = 2 * ∑ i ∈ Finset.range 4, (n + i) + 15) :
    n = 6 := by
  norm_num [Finset.sum_range_succ] at h
  omega