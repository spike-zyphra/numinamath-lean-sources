import Mathlib

open Real

theorem inequalities_222024 (x y z : ℝ) :
    x^2 + y^2 + z^2 ≥ sqrt 2 * (x * y + y * z) := by 
  nlinarith [sq_nonneg (x - z), sq_nonneg (x + z), sq_nonneg (y - (x * Real.sqrt 2)), sq_nonneg (y - (z * Real.sqrt 2)), sq_nonneg (x - z), sq_nonneg (x * Real.sqrt 2 - y), sq_nonneg (z * Real.sqrt 2 - y), sq_nonneg (x - z), sq_nonneg (y - (x + z) * Real.sqrt 2 / 2), sq_nonneg (x - z), sq_nonneg (x - (Real.sqrt 2 / 2) * y), sq_nonneg (z - (Real.sqrt 2 / 2) * y), 
          sq_nonneg (x + z - 2 * (z)), sq_nonneg (y * Real.sqrt 2 - x - z), 
          Real.sqrt_nonneg 2, 
          sq_nonneg (y), 
          sq_nonneg (x - z), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]