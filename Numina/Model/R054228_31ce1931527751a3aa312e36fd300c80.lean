import Mathlib

theorem algebra_301365 (x y : ℝ) (h : x^2 + x * y + y^2 = 3) :
    x^2 - x * y + y^2 ∈ Set.Icc 1 9 := by 
  have h1 : x^2 + y^2 = 3 - x * y := by
    nlinarith
  have h2 : x^2 - x * y + y^2 = 3 - 2 * (x * y) := by
    nlinarith [h1]
  have h4 : x * y ≤ 1 := by
    nlinarith [sq_nonneg (x - y)]
  have h5 : x * y ≥ -3 := by 
    nlinarith [sq_nonneg (x + y)]
  rw [h2]
  constructor
  · -- Show that 1 ≤ 3 - 2 * (x * y)
    nlinarith
  · -- Show that 3 - 2 * (x * y) ≤ 9
    nlinarith