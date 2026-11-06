import Mathlib

theorem algebra_17029 (x y : ℝ) (hx : x = 4 * 3 + 2 * 2) (hy : y = 6 * 3 + 2 * 2) :
    ⌈2 * (x + y) / 12⌉ = 7 := by 
  rw [hx, hy]
  norm_num [Int.ceil_eq_iff]