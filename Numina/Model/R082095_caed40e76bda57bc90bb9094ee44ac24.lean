import Mathlib

theorem algebra_278406 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : 17 * 3 = x * 30 + y * 3) (h2 : 2 * 30 = x * 75 + y * 30) :
    x * 75 = 17 * 3 := by 
  linarith