import Mathlib

theorem algebra_179439 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (hxy : x * 3 = y * 2) (h : x * 40 = y * 60) :
    x = 4 := by 
  nlinarith