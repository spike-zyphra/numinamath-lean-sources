import Mathlib

theorem algebra_306505 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x^2 + (Real.sqrt 2 - 1) * x * y - Real.sqrt 2 * y^2 + (Real.sqrt 2 / 2) * x - (2 * Real.sqrt 2 + 1) * y - 1 = 0) :
    20 + 12 * Real.sqrt 2 ≠ 0 := by
  have h1 : 0 < Real.sqrt 2 := by positivity
  have h2 : 0 < 12 * Real.sqrt 2 := by positivity
  have h3 : 0 < 20 + 12 * Real.sqrt 2 := by linarith
  linarith