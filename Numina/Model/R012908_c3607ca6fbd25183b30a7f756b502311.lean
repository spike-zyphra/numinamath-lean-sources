import Mathlib

theorem algebra_316985 (x y z : ℝ) (h : x^2 + 2*y^2 + 3*z^2 = 24) :
    x + 2*y + 3*z ≥ -12 := by 
  nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (z + 2),
          sq_nonneg (x + 2 - (y + 2)), sq_nonneg (y + 2 - (z + 2)), 
          sq_nonneg (x + 2 - 2*(y + 2)), sq_nonneg (2*(y + 2) - 3*(z + 2)), 
          sq_nonneg ((x + 2*y + 3*z)), 
          sq_nonneg (x + 2*y + 3*z + 12)]