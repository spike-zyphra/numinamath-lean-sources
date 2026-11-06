import Mathlib

theorem algebra_67497 (x : ℤ) (h : ∑ i ∈ Finset.range 20, (x + i + 1) = ∑ i ∈ Finset.range 10, (174 + 2 * i)) :
    x = 81 := by 
  norm_num [Finset.sum_range_succ] at h 
  linarith