import Mathlib

theorem algebra_11573 (n : ℕ) (h : n = 12) :
    ∑ i in Finset.range n, (i + 1) = 78 := by 
  rw [h]
  norm_num [Finset.sum_range_succ]