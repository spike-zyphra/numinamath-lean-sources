import Mathlib

theorem inequalities_149414 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y) * Real.sqrt ((y + z) * (z + x)) +
    (y + z) * Real.sqrt ((z + x) * (x + y)) +
    (z + x) * Real.sqrt ((x + y) * (y + z)) ≥
    4 * (x * y + y * z + z * x) := by

  have h1 : 0 ≤ (x + y) * Real.sqrt ((y + z) * (z + x)) - x * (y + z) - y * (z + x) := by
    nlinarith [Real.sqrt_nonneg ((y + z) * (z + x)), Real.mul_self_sqrt (by positivity : 0 ≤ (y + z) * (z + x)), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), mul_pos (show 0 < x * y by nlinarith) (show 0 < z by assumption)]
  
  have h2 : 0 ≤ (y + z) * Real.sqrt ((z + x) * (x + y)) - y * (z + x) - z * (x + y) := by
    nlinarith [Real.sqrt_nonneg ((z + x) * (x + y)), Real.mul_self_sqrt (by positivity : 0 ≤ (z + x) * (x + y)), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, sq_nonneg (y - z), sq_nonneg (y - x), sq_nonneg (z - x), mul_pos (show 0 < y * z by nlinarith) (show 0 < x by assumption)]
  
  have h3 : 0 ≤ (z + x) * Real.sqrt ((x + y) * (y + z)) - z * (x + y) - x * (y + z) := by
    nlinarith [Real.sqrt_nonneg ((x + y) * (y + z)), Real.mul_self_sqrt (by positivity : 0 ≤ (x + y) * (y + z)), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, sq_nonneg (z - x), sq_nonneg (z - y), sq_nonneg (x - y), mul_pos (show 0 < z * x by nlinarith) (show 0 < y by assumption)]
  
  linarith [h1, h2, h3]