import Mathlib

theorem inequalities_149438 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^3 + z^3 + y^3 ≥ x^2 * Real.sqrt (y * z) + z^2 * Real.sqrt (x * y) + y^2 * Real.sqrt (x * z) := by
  nlinarith [sq_nonneg (x - Real.sqrt (y * z)), sq_nonneg (y - Real.sqrt (x * z)), sq_nonneg (z - Real.sqrt (x * y)), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z), 
          Real.sq_sqrt (show 0 ≤ y * z by nlinarith), Real.sq_sqrt (show 0 ≤ x * y by nlinarith), Real.sq_sqrt (show 0 ≤ x * z by nlinarith),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_nonneg (Real.sqrt_nonneg (y * z)) (Real.sqrt_nonneg (x * y)), 
          mul_nonneg (Real.sqrt_nonneg (y * z)) (Real.sqrt_nonneg (x * z)), 
          mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (x * z)), 
          sq_nonneg (Real.sqrt (y * z) - Real.sqrt (x * y)), sq_nonneg (Real.sqrt (y * z) - Real.sqrt (x * z)), sq_nonneg (Real.sqrt (x * y) - Real.sqrt (x * z))
        ]