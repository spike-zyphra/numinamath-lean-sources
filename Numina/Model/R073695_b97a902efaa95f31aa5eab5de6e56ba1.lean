import Mathlib

theorem algebra_96140 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 5 * y = k / x ^ 2) (hk : k = 5 * 16) :
    5 * (1 / 4) = k / 8 ^ 2 := by
  rw [hk]
  norm_num