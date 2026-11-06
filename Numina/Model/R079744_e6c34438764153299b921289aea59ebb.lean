import Mathlib

theorem algebra_237126 (n : ℕ) (h : Odd n) (h' : ∑ i ∈ Finset.range 7, (n + 2 * i) = 105) :
    n + 2 * 6 = 21 := by
  norm_num [Finset.sum_range_succ] at h'
  omega