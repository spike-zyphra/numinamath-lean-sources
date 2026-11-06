import Mathlib

theorem algebra_243871 {x : ℝ} (hx : x > 0) (h : 12 * x + 10 * x = 12 * (x * 0.98) + 10 * (x * 1.1)) :
    (12 * (x * 0.98) + 10 * (x * 1.1)) / (12 * x + 10 * x) = 1.04 := by
  ring_nf at h 
  have h2 : x = 0 := by 
    linarith 
  linarith