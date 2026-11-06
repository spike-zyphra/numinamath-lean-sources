import Mathlib

theorem algebra_252768 {x y : ℝ} (h : (x + y)^2 - (x - y)^2 = 20) : x * y = 5 := by
  have eq1 : (x + y) ^ 2 = x^2 + 2 * x * y + y^2 := by ring
  have eq2 : (x - y) ^ 2 = x^2 - 2 * x * y + y^2 := by ring
  rw [eq1, eq2] at h 
  linarith