import Mathlib

theorem algebra_1314 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h1 : 60 * 24 = x * 24 + y * 60) (h2 : 30 * 60 = x * 60 + y * 120) :
    x = 20 := by 
  nlinarith