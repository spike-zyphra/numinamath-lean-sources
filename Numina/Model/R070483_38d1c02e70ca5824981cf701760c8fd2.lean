import Mathlib

theorem algebra_298269 (x : ℝ) (hx : x > 0) (h : (x - 800) * 0.14 = 420) :
    x = 3800 := by
  norm_num at h ⊢
  linarith