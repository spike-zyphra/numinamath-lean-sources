import Mathlib

theorem algebra_177334 (n : ℕ) (h : ∑ i ∈ Finset.range 5, (n + i) = 2010) :
    n + 4 = 404 := by 
  norm_num [Finset.sum_range_succ] at h 
  omega