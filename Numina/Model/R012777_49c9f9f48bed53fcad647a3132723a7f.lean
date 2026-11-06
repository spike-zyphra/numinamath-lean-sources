import Mathlib

theorem algebra_263366 (x y : ℝ) (h : x^2 + y^2 ≤ 1) :
    |x^2 + 2 * x * y - y^2| ≤ √2 := by
  have h1 : -Real.sqrt 2 ≤ x^2 + 2 * x * y - y^2 := by
    nlinarith [sq_nonneg (x^2 + 2 * x * y - y^2 + Real.sqrt 2), 
            sq_nonneg (x - y), 
            sq_nonneg (x + y), 
            sq_nonneg (x * (x - y) + y * (x + y)), 
            sq_nonneg ((x + y) - (x - y)), 
            sq_nonneg ((x - y) + (x + y)), 
            sq_nonneg ((x^2 + y^2) - 1), 
            Real.sqrt_nonneg 2, 
            Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
            sq_nonneg (x^2 - y^2 - 2 * x * y), 
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
            sq_nonneg (x^2 - y^2 + 2 * x * y), 
            Real.sqrt_nonneg 2]
  have h2 : x^2 + 2 * x * y - y^2 ≤ Real.sqrt 2 := by
    nlinarith [sq_nonneg (x^2 + 2 * x * y - y^2 - Real.sqrt 2), 
            sq_nonneg (x - y), 
            sq_nonneg (x + y), 
            sq_nonneg (x * (x - y) + y * (x + y)), 
            sq_nonneg ((x + y) - (x - y)), 
            sq_nonneg ((x - y) + (x + y)), 
            sq_nonneg ((x^2 + y^2) - 1), 
            Real.sqrt_nonneg 2, 
            Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
            sq_nonneg (x^2 - y^2 - 2 * x * y), 
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
            sq_nonneg (x^2 - y^2 + 2 * x * y), 
            Real.sqrt_nonneg 2]
  apply abs_le.mpr
  constructor <;> 
    linarith [h1, h2]