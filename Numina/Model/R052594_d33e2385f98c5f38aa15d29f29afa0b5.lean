import Mathlib

open Real

theorem inequalities_263109 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    sqrt (7 * x + 3) + sqrt (7 * y + 3) + sqrt (7 * z + 3) ≤ 7 := by

  nlinarith [sq_nonneg (sqrt (7 * x + 3) - sqrt (7 * y + 3)), 
          sq_nonneg (sqrt (7 * y + 3) - sqrt (7 * z + 3)), 
          sq_nonneg (sqrt (7 * x + 3) - sqrt (7 * z + 3)), 
          Real.sq_sqrt (show (7 * x + 3 : ℝ) ≥ 0 by nlinarith), 
          Real.sq_sqrt (show (7 * y + 3 : ℝ) ≥ 0 by nlinarith), 
          Real.sq_sqrt (show (7 * z + 3 : ℝ) ≥ 0 by nlinarith), 
          Real.sqrt_nonneg (7 * x + 3), 
          Real.sqrt_nonneg (7 * y + 3), 
          Real.sqrt_nonneg (7 * z + 3), 
          hsum, 
          mul_nonneg (Real.sqrt_nonneg (7 * x + 3)) (Real.sqrt_nonneg (7 * y + 3)), 
          mul_nonneg (Real.sqrt_nonneg (7 * y + 3)) (Real.sqrt_nonneg (7 * z + 3)), 
          mul_nonneg (Real.sqrt_nonneg (7 * x + 3)) (Real.sqrt_nonneg (7 * z + 3))
]