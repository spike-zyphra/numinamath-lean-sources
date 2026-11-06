import Mathlib

theorem algebra_98496 (n : ℕ) (h : Even n) (h' : ∑ i ∈ Finset.range 25, (n + 2 * i) = 10000) :
n + 2 * 24 = 424 := by
  norm_num [Finset.sum_range_succ] at h'
  have eq1 : 25 * n = 9400 := by 
    linear_combination h'
  have eq2 : n = 376 := by
    omega
  omega