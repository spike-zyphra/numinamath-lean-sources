import Mathlib

theorem algebra_685 (x : ℝ) (hx : x ≠ 0) (h1 : x * (1 - 1 / 2) * (1 - 1 / 3) * (1 - 1 / 4) * (1 - 1 / 5) = 6) :
    x = 30 := by
  norm_num at h1
  linarith