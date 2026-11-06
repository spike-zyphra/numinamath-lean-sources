import Mathlib

theorem inequalities_8997
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x + y) * Real.sqrt ((z + x) * (z + y)) +
    (y + z) * Real.sqrt ((x + y) * (x + z)) +
    (z + x) * Real.sqrt ((y + z) * (y + x)) ≥
    4 * (x * y + y * z + z * x) := by
  have h1 : 0 < (z + x) * (z + y) := by positivity
  have h2 : 0 < (x + y) * (x + z) := by positivity
  have h3 : 0 < (y + z) * (y + x) := by positivity
  have h4 : Real.sqrt ((z + x) * (z + y)) = Real.sqrt (z + x) * Real.sqrt (z + y) := by
    rw [Real.sqrt_mul (by positivity)]
  have h5 : Real.sqrt ((x + y) * (x + z)) = Real.sqrt (x + y) * Real.sqrt (x + z) := by
    rw [Real.sqrt_mul (by positivity)]
  have h6 : Real.sqrt ((y + z) * (y + x)) = Real.sqrt (y + z) * Real.sqrt (y + x) := by
    rw [Real.sqrt_mul (by positivity)]
  rw [h4, h5, h6]
  nlinarith [sq_nonneg (Real.sqrt (z + x) - Real.sqrt (z + y)), 
          sq_nonneg (Real.sqrt (x + y) - Real.sqrt (x + z)), 
          sq_nonneg (Real.sqrt (y + z) - Real.sqrt (y + x)), 
          Real.sqrt_nonneg (z + x), Real.sqrt_nonneg (z + y), 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (x + z), 
          Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (y + x), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (z + y)), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (x + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (y + x)), 
          Real.sq_sqrt (show 0 ≤ z + x by positivity), 
          Real.sq_sqrt (show 0 ≤ z + y by positivity), 
          Real.sq_sqrt (show 0 ≤ x + y by positivity), 
          Real.sq_sqrt (show 0 ≤ x + z by positivity), 
          Real.sq_sqrt (show 0 ≤ y + z by positivity), 
          Real.sq_sqrt (show 0 ≤ y + x by positivity), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
        ]