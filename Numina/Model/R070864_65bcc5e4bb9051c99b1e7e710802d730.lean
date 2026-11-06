import Mathlib

theorem algebra_117564 {x y : ℝ} (h1 : 2*x=3*y) (h2 : y=12*x) :
    18*x=27*y := by
  linarith [h1, h2]