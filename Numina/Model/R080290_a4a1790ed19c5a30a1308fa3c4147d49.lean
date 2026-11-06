import Mathlib

theorem algebra_179801 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 20 * 60 = x * 60 + y * 35) (h2 : 30 * 35 = x * 35 + y * 20) :
    (6 * 30 + 10 * 84) = x * 30 + y * 20 := by 
  linarith