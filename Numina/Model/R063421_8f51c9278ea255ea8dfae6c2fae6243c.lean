import Mathlib

theorem inequalities_4010 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y + z)^2 / (x * y + x * z + y * z) ≥
    9 * (z^2 + 2 * x * y) / (2 * x^2 + 2 * y^2 + 2 * z^2 + y * z + x * z + x * y) := by
  have h1 : 0 < x * y + x * z + y * z := by
    positivity
  have h2 : 0 < 2 * x^2 + 2 * y^2 + 2 * z^2 + y * z + x * z + x * y := by
    positivity
  apply (div_le_div_iff (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (z * (x - y)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
          sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2)]