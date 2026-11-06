import Mathlib

theorem algebra_171875 (n : ℕ) (h : Even n) (h' : ∑ i ∈ Finset.range 7, (n + 2 * i) = 1988) :
    n + 2 * 6 = 290 := by
  norm_num [Finset.sum_range_succ] at h'
  omega