import Mathlib

theorem algebra_101802 {x y : ℝ} (hx : x^3 - 3*x^2 + 5*x = 1) (hy : y^3 - 3*y^2 + 5*y = 5) : x + y = 2 := by 
  have hxy : x^3 - 3*x^2 + 5*x + y^3 - 3*y^2 + 5*y = 6 := by linarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]