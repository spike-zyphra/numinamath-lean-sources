import Mathlib

theorem algebra_598147 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : (1 + 20 / 100) * x = (1 + 20 / 100) * y / 2) :
    (1 + 40 / 100) * x < y := by
  nlinarith