import Mathlib

theorem algebra_11857 {x y : ℝ} (h : x * (x + y) = x ^ 2 + 8) : x * y = 8 := by
  have eq1 : x * (x + y) = x^2 + x * y := by
    ring
  have eq2 : x^2 + x * y = x^2 + 8 := by
    linarith [h, eq1]
  have eq3 : x * y = 8 := by
    linarith [eq2]
  linarith [eq3]