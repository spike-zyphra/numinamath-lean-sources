import Mathlib

theorem algebra_216133 {x : ℝ} (hx : x > 0) (h : (1 - x) * 2 / 100 + x * 3 / 100 = (1 - x) * 1.5 / 100 + x * 2 / 100) :
    x = 1 / 2 := by
  norm_num at h ⊢
  linarith