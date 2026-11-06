import Mathlib

theorem algebra_1475 (x y : ℝ) (h₀ : x^3 + y^3 = 1000) (h₁ : x^2 * y - x * y^2 = -496) :
    (x^3 - y^3) + (4 * x * y^2 - 2 * x^2 * y) - 2 * (x * y^2 - y^3) = 1992 := by 
  -- simplifying the left side
  have h2 : (x^3 - y^3) + (4 * x * y^2 - 2 * x^2 * y) - 2 * (x * y^2 - y^3) = (x^3 + y^3) - 2 * (x^2 * y - x * y^2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  rw [h2]
  rw [h₀, h₁]
  norm_num