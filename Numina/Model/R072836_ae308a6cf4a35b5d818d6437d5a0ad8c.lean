import Mathlib

theorem algebra_141326 {x : ℕ} (hx : x > 0) (h : ∑ i ∈ Finset.range 22, (i + 1) * x = 6710000 + 110000) :
    x = 500000 := by
  norm_num [Finset.sum_range_succ] at h
  omega