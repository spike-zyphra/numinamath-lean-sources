import Mathlib

theorem algebra_294807 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 16 * 20 = x * 20 + y * 16) (h2 : 20 * 15 = x * 15 + y * 20)
    (h3 : 12 * 5 = x * 5 + y * 12) :
    (12 * 10 = x * 10 + y * 12) := by 
  linarith