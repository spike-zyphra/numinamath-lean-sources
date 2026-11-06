import Mathlib

theorem algebra_217670 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hA : x * 40 - 2 * y = y * 26 - x) (hB : x * 30 + 10 * y = y * 150 + 30 * x) :
    x * 150 + 30 * y = 133.7 := by
  nlinarith