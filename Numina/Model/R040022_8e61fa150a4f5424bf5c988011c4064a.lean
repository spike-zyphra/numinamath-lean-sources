import Mathlib

open Real

theorem inequalities_105220 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1 / x + 1 / y + 1 / z) :
    x + y + z ≥ sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) +
    sqrt ((z * x + 1) / 2) := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : x + y + z = (x * y + y * z + z * x) / (x * y * z) := by
    field_simp at h ⊢
    nlinarith [h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h1]
  have h3 : x * y * z * (x + y + z) = x * y + y * z + z * x := by
    field_simp at h2 ⊢
    nlinarith
  nlinarith [sq_nonneg (sqrt ((x * y + 1) / 2) - x), sq_nonneg (sqrt ((y * z + 1) / 2) - y), sq_nonneg (sqrt ((z * x + 1) / 2) - z), 
          Real.sqrt_nonneg ((x * y + 1) / 2), Real.sqrt_nonneg ((y * z + 1) / 2), Real.sqrt_nonneg ((z * x + 1) / 2), 
          Real.sq_sqrt (show (x * y + 1) / 2 ≥ 0 by positivity), 
          Real.sq_sqrt (show (y * z + 1) / 2 ≥ 0 by positivity), 
          Real.sq_sqrt (show (z * x + 1) / 2 ≥ 0 by positivity), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          mul_nonneg (show 0 ≤ (x * y + 1) / 2 by positivity) (show 0 ≤ (y * z + 1) / 2 by positivity), 
          Real.sqrt_le_sqrt (show (x * y + 1) / 2 ≥ 0 by positivity), Real.sqrt_le_sqrt (show (y * z + 1) / 2 ≥ 0 by positivity), h2, h, h1, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]