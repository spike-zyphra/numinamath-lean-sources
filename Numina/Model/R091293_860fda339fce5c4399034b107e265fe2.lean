import Mathlib

theorem algebra_264735 {x : ℝ} (hx : x > 180000) (h : (1 + 25 / 100) * x = (1 + 16 / 100) * (x - 20 / 100)) :
    x = 100 := by
  norm_num at h 
  linarith