import Mathlib

theorem algebra_309420 (x y : ℝ) (h : (2015 + x^2) * (2015 + y^2) = 2^22) :
    x + y ≤ 2 * Real.sqrt 33 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 33), sq_nonneg (x + y - 2 * Real.sqrt 33), 
          Real.sqrt_nonneg 33, 
          Real.sq_sqrt (show 0 ≤ 33 by norm_num), 
          sq_nonneg (x - Real.sqrt 33), sq_nonneg (y - Real.sqrt 33), 
          sq_nonneg (x + y - 2 * Real.sqrt 33), 
          mul_nonneg (Real.sqrt_nonneg 33) (Real.sqrt_nonneg 33)]