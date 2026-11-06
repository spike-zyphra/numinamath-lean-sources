import Mathlib

theorem algebra_303084 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0)
    (hxy : x * 5 + y * 2 ≤ 200) (hxy' : x * 2 + y * 8 ≤ 160) (hxy'' : x * 3 + y * 5 ≤ 150) :
    x * 7 + y * 10 ≤ 336 + 16 / 19 := by 
  linarith