import Mathlib

theorem algebra_6927 (x : ℕ) (hx : x > 0) (h : 2 + ∑ i ∈ Finset.range 5, (2 * (2 ^ i) - 1) ≤ x) :
    x ≥ 37 := by
  norm_num [Finset.sum_range_succ] at h
  omega