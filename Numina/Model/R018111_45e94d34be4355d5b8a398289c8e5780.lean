import Mathlib

open Real

theorem inequalities_109350 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y) * sqrt ((z + x) * (z + y)) + (y + z) * sqrt ((x + y) * (x + z)) +
    (z + x) * sqrt ((y + z) * (y + x)) ≥ 4 * (x * y + y * z + z * x) := by
  have h4 : sqrt ((z + x) * (z + y)) = Real.sqrt (z + x) * Real.sqrt (z + y) := by
    rw [Real.sqrt_mul (by positivity)]
  have h5 : sqrt ((x + y) * (x + z)) = Real.sqrt (x + y) * Real.sqrt (x + z) := by
    rw [Real.sqrt_mul (by positivity)]
  have h6 : sqrt ((y + z) * (y + x)) = Real.sqrt (y + z) * Real.sqrt (y + x) := by 
    rw [Real.sqrt_mul (by positivity)]
  rw [h4, h5, h6]
  nlinarith [mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (z + y)), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (x + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (y + x)), 
          sq_nonneg (Real.sqrt (z + x) - Real.sqrt (z + y)), 
          sq_nonneg (Real.sqrt (x + y) - Real.sqrt (x + z)), 
          sq_nonneg (Real.sqrt (y + z) - Real.sqrt (y + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + z)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (y + x)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          Real.sqrt_nonneg (z + x), Real.sqrt_nonneg (z + y), 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (x + z), 
          Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (y + x), 
          sq_nonneg ((x - y) + (y - z) + (z - x)), 
          sq_nonneg (Real.sqrt (z + x) ^ 2 - (z + x)), 
          sq_nonneg (Real.sqrt (z + y) ^ 2 - (z + y)), 
          sq_nonneg (Real.sqrt (x + y) ^ 2 - (x + y)), 
          sq_nonneg (Real.sqrt (x + z) ^ 2 - (x + z)), 
          sq_nonneg (Real.sqrt (y + z) ^ 2 - (y + z)), 
          sq_nonneg (Real.sqrt (y + x) ^ 2 - (y + x)), 
          Real.sq_sqrt (show 0 ≤ (z + x : ℝ) by positivity), 
          Real.sq_sqrt (show 0 ≤ (z + y : ℝ) by positivity), 
          Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by positivity), 
          Real.sq_sqrt (show 0 ≤ (x + z : ℝ) by positivity), 
          Real.sq_sqrt (show 0 ≤ (y + z : ℝ) by positivity), 
          Real.sq_sqrt (show 0 ≤ (y + x : ℝ) by positivity)
        ]