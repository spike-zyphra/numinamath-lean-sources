import Mathlib

theorem algebra_274465 (a b c w : ℝ) (ha : a ≠ 0) (h1 : a * (-1) ^ 2 + b * (-1) + c = 0)
    (h2 : a * 4 ^ 2 + b * 4 + c = 0) (h3 : c = 8) (h4 : a * 3 ^ 2 + b * 3 + c = w) :
    w = 8 := by 
  subst c
  linarith