import Mathlib

theorem algebra_301631 (x y : ℝ) (h : x^2 + x * y + y^2 = 3) :
    x^2 - x * y + y^2 ∈ Set.Icc 1 9 := by 
  have h1 : x^2 + y^2 ≥ 2 * (x * y) := by 
    linarith [sq_nonneg (x - y)]
  have h2 : x * y ≤ 1 := by 
    nlinarith [h, h1]
  have h3 : x^2 + y^2 ≥ -2 * (x * y) := by 
    nlinarith [sq_nonneg (x + y)]
  have h4 : x * y ≥ -3 := by 
    nlinarith [h, h3]
  have h5 : x^2 - x * y + y^2 ≥ 1 := by 
    nlinarith [h, h4, h2]
  have h6 : x^2 - x * y + y^2 ≤ 9 := by 
    nlinarith [h, h4, h2]
  constructor 
  · -- Show that 1 ≤ x^2 - x * y + y^2
    linarith [h5]
  · -- Show that x^2 - x * y + y^2 ≤ 9
    linarith [h6]