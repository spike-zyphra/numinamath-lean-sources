import Mathlib

theorem algebra_268546 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0)
    (h : 10*x+8*y=1222.50) :
    8*y=1222.50-10*x := by
  linarith