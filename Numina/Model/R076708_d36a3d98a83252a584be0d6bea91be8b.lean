import Mathlib

theorem algebra_236355 (x : ℝ) (hx : x > 0) (h : (3 + x) * 0.4 = 3 * 0.1 + x) :
    x = 1.5 := by
  norm_num at h ⊢
  linarith