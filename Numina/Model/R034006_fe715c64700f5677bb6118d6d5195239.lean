import Mathlib

theorem algebra_317521 {x y : ℝ} (h₀ : (x - 1)^5 + 1999 * (x - 1) = 2519) (h₁ : (y - 1)^5 + 1999 * (y - 1) = -2519) : x + y = 2 := by
  have h2 : (x - 1) ^ 5 + 1999 * (x - 1) + ((y - 1) ^ 5 + 1999 * (y - 1)) = 0 := by 
    linarith
  have h_eq : x - 1 = -(y - 1) := by 
    nlinarith [sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) - (y - 1)), 
              sq_nonneg ((x - 1)^2 - (y - 1)^2), sq_nonneg ((x - 1)^3 - (y - 1)^3), 
              sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1)^2 + (y - 1)^2), 
              sq_nonneg ((x - 1)*(y - 1))]
  linarith