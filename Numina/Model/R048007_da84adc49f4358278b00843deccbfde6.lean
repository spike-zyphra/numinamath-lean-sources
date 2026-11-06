import Mathlib

theorem algebra_323597 (x y : ℝ) (h : x^2 + 2 * √3 * x * y - y^2 = 3) :
    x^2 + y^2 ≥ 3 / 2 := by
  nlinarith [sq_nonneg (x - y / √3), sq_nonneg (√3 * y + 3 * x), sq_nonneg (x + y / √3), sq_nonneg (√3 * x + y), sq_nonneg (√3 * y + x), sq_nonneg (√3 * y - √3 * x), sq_nonneg (√3 * x - y), 
          sq_nonneg (x + √3 * y), sq_nonneg (x - √3 * y), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          sq_nonneg (x^2 + y^2 - 3 / 2), 
          sq_nonneg (√3 * (x^2 + y^2) - 3 / 2), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)
        ]