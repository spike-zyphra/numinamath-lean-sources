import Mathlib

theorem algebra_111048 {x y : ℝ} (h : x ≠ 0) (h1 : 2 * x - y - 2 = 0) (h2 : x + y + 3 = 0)
    (h3 : (x - 3) ^ 2 + y ^ 2 = (x + 3) ^ 2 + (y - 2) ^ 2) :
    8 * x - y - 24 = 0 := by 
  nlinarith