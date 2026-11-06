import Mathlib

theorem algebra_173565 {x y : ℝ} (hy : y ≠ 0) (h : x + y = 2000) (h' : x + (0.8 * y) = 1760) :
    x = 800 := by 
  ring_nf at h h'
  linarith