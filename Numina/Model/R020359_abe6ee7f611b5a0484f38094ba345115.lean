import Mathlib

theorem algebra_165971 {x : ℝ} (hx : x > 0) (h1 : 100 / 100 * x = 1.44 * (x - 100)) (h2 : 90 / 100 * x = 1.44 * (x - 360)) :
    x = 1000 := by
  norm_num at h1 h2 
  linarith