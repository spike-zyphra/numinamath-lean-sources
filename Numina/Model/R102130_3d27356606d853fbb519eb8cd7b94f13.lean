import Mathlib

theorem algebra_252986 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 100 = y * 120 - x) (h2 : y * 120 = x * 100 + y) :
    x = 500 := by 
  nlinarith