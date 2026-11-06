import Mathlib

theorem algebra_7020 {a r : ℚ} (ha : a = 2) (hr : r = 4) :
    ∏ i ∈ Finset.range 10, a * r ^ i = 2 ^ 100 := by 
  rw [ha, hr]
  norm_num [Finset.prod_range_succ]