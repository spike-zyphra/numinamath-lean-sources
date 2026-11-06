import Mathlib

theorem algebra_268761 (a : ℕ) (ha : a > 0) (h : ∑ i ∈ Finset.range 37, (a + 3 * i) = 2011 - (a + 3 * 33)) :
    a + 3 * 33 = 34 := by
  norm_num [Finset.sum_range_succ] at h
  omega