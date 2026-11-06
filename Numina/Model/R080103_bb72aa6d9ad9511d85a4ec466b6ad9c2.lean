import Mathlib

theorem algebra_6713 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0)
    (h1 : x + 2 * y ≤ 6) (h2 : 4 * x + 3 * y ≤ 12) :
    7 * x + 5 * y ≤ 21 := by 
  linarith