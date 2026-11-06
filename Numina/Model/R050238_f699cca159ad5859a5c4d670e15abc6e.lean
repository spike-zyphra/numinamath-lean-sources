import Mathlib

theorem algebra_7426 (a m n : ℕ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n)
    (h : ∑ i ∈ Finset.range 19, (a + m * i) + ∑ i ∈ Finset.range 19, (a + n * (18 - i)) = 2010) :
    a = 105 := by
  norm_num [Finset.sum_range_succ] at h 
  omega