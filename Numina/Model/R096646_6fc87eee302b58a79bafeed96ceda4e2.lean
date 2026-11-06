import Mathlib

theorem algebra_93266 {x : ℝ} (hx : x > 0) (h : (1 - 25 / 100) * x = (1 - 20 / 100) * (x / (1 - 25 / 100)) + (1 + 25 / 100) * x) :
    x = 125 / 100 := by
  norm_num at h
  nlinarith