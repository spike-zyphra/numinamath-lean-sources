import Mathlib

theorem algebra_104624 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x + y = 6) (h2 : y = 10) :
    x = 15 := by 
  linarith