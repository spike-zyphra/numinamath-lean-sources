import Mathlib

theorem algebra_169270 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x*10+y*8+z*5=7) (h' : z≤2) :
    x≤1 := by
  linarith