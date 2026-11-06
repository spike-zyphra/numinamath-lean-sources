import Mathlib

open Real

theorem inequalities_110794 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^2 + y^2 + 1 ≥ x * sqrt (y^2 + 1) + y * sqrt (x^2 + 1) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x^2 + y^2 - 1),
          Real.sqrt_nonneg (y^2 + 1), Real.sqrt_nonneg (x^2 + 1),
          Real.sq_sqrt (show (y^2 + 1) ≥ 0 by positivity),
          Real.sq_sqrt (show (x^2 + 1) ≥ 0 by positivity),
          sq_nonneg (sqrt (y^2 + 1) - sqrt (x^2 + 1)), 
          sq_nonneg (x - sqrt (y^2 + 1)), 
          sq_nonneg (y - sqrt (x^2 + 1)),
          mul_nonneg (Real.sqrt_nonneg (y^2 + 1)) (Real.sqrt_nonneg (x^2 + 1)), 
          Real.sqrt_nonneg ((y^2 + 1) * (x^2 + 1)), 
          sq_nonneg (x * sqrt (y^2 + 1) - y * sqrt (x^2 + 1)), 
          sq_nonneg (x * sqrt (y^2 + 1) + y * sqrt (x^2 + 1) - (x^2 + y^2 + 1))
          ]