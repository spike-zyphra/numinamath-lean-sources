import Mathlib

theorem algebra_20332 {x y : ℝ} (hx : x^2 / 16 - y^2 / 9 = 1) (h : (x - 5)^2 + y^2 = 25 / 4 * (x - 16 / 5)^2 + 9 / 4 * y^2) :
    x^2 / 16 - y^2 / 9 = 1 := by
  exact hx