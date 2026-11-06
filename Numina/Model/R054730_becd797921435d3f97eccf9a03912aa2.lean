import Mathlib

theorem algebra_125109 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : x * 40 + y * 50 = x * 4 + y * 40) :
    y / (x + y) = 1 / 7 := by

  have h1 : 36 * x + 10 * y = 0 := by
    nlinarith
  have h2 : 36 * x + 10 * y > 0 := by
    nlinarith
  linarith