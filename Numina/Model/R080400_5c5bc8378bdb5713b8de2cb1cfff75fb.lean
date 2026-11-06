import Mathlib

theorem algebra_44199 (A : ℕ) (hA : A > 0) (h : ∑ i ∈ Finset.range 11, A = ∑ i ∈ Finset.range 11, (3 * (i + 1))^2) :
    A = 414 := by
  norm_num [Finset.sum_range_succ] at h
  omega