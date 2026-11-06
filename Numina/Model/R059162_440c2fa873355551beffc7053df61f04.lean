import Mathlib

theorem number_theory_193899 (Q : ℤ) (h : Q ≠ 0) (h' : ∑ i ∈ Finset.range 100, (i + 1) * Q = 100 * Q) :
    Q = 10001 := by 
  norm_num [Finset.sum_range_succ] at h' 
  omega