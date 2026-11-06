import Mathlib

theorem algebra_13713 {x y : ℝ} (h1 : 2*x+3*y=2.50) (h2 : 3*x+2*y=2.70) :
    3*x+4*y=3.54 := by
  ring_nf at h1 h2 ⊢
  linarith