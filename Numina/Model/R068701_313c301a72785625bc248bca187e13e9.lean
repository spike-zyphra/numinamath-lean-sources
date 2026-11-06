import Mathlib

theorem algebra_126647 (x : ℝ) (hx : x ≠ 0) (h1 : (0.2 * x + 16) + (0.3 * (x - (0.2 * x + 16)) + 20) + (0.75 * (x - (0.2 * x + 16) - (0.3 * (x - (0.2 * x + 16)) + 20)) + 30) = x) :
    x = 270 := by
  ring_nf at h1 
  linarith