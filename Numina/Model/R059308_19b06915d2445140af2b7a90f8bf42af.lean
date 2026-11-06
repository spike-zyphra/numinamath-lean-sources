import Mathlib

theorem algebra_278253 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x * 100 = y * 100 - 2) (h2 : x = y + 4.2) :
    x = 5.97 := by
  norm_num at h1 h2 ⊢
  linarith