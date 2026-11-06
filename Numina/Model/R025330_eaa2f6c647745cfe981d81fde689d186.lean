import Mathlib

theorem algebra_212743 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (1 - 40 / 100) * x = y) (h2 : (1 - 20 / 100) * y = (1 / 2) * x)
    (h3 : (1 - 40 / 100) * x = (1 - 20 / 100) * y + 26) (h4 : (1 - 20 / 100) * y > (1 + 5 / 100) * x) :
    x = 60 := by
  nlinarith