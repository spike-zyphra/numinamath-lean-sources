import Mathlib

theorem algebra_290441 {x : ℕ} (hx : x > 0) (h : ∑ i ∈ Finset.range 31, (if i < 15 then x + 3 * i else x + 4 * (30 - i)) = 2012) :
    x + 3 * 15 = 92 := by
  norm_num [Finset.sum_range_succ] at h
  omega