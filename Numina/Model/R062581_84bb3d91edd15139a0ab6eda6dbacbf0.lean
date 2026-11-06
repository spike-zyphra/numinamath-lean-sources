import Mathlib

theorem algebra_115046 {x : ℝ} (hx : x > 0) (h : (1 - 0.08) * (1 + (x / 100)) = (1 + ((x + 10) / 100))) :
    x = 15 := by
  ring_nf at h 
  linarith