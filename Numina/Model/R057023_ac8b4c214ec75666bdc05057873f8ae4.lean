import Mathlib

theorem algebra_130817 {x : ℝ} (hx : x > 0) (h : (1 - 80 / 100) * (1 - x / 1000) = 50 / 100) :
    x = 375 := by
  norm_num at h ⊢
  linarith