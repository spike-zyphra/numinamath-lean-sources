import Mathlib

theorem algebra_303802 (x y : ℝ) (h : x^2 + x * y + y^2 = 3) :
    1 ≤ x^2 - x * y + y^2 ∧ x^2 - x * y + y^2 ≤ 9 := by
  -- The approach consists of converting the quadratic expressions to variables and using inequalities
  have h1 : x^2 - x * y + y^2 = 9 - 2 * (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
  have h2 : (x + y) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  have h3 : 1 ≤ x^2 - x * y + y^2 := by
    nlinarith [h1, h2]
  have h4 : x^2 - x * y + y^2 ≤ 9 := by
    nlinarith [h1, h2]
  exact ⟨h3, h4⟩