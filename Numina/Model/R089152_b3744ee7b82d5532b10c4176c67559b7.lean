import Mathlib

theorem algebra_43 (x y : ℝ) (h₀ : 1 ≤ y) (h₁ : y ≤ x) (h₂ : 2*x^2 - x*y - 5*x + y + 4 = 0) : x + y = 4 := by
  have h3 : (x - 2) ^ 2 + (y - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - 1), sq_nonneg (x - 2), sq_nonneg (y - 2)]
  have hx : x - 2 = 0 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2)]
  have hy : y - 2 = 0 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2)]
  have hx2 : x = 2 := by 
    linarith
  have hy2 : y = 2 := by 
    linarith
  linarith [hx2, hy2]