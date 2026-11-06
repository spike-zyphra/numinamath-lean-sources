import Mathlib

theorem algebra_15308 {x : ℝ} (hx : x = 2) :
    (∏ i ∈ Finset.range 15, x^(i + 1)) / (∏ i ∈ Finset.range 10, x^(2 * i + 2)) = 1024 := by
  rw [hx]
  norm_num [Finset.prod_range_succ]