import Mathlib

theorem algebra_270771 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 4 = y * 5 + 6) (h2 : x * 31 = y * 4 + 6) :
    x = 12 ∧ y = 18 := by
  nlinarith