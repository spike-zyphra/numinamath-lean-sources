import Mathlib

theorem inequalities_268291 (x y : ℝ) (h : x^3 + y^3 ≤ 2) : x + y ≤ 2 := by
  by_contra h1
  -- So we have h1 : x + y > 2
  have h2 : x + y > 2 := by linarith
  -- Expanding the sum of cubes: x^3 + y^3 = (x+y)^3 - 3xy(x+y)
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x*y), sq_nonneg (x^2 - y^2), sq_nonneg (x*y - 1), sq_nonneg (x + y - 2)]