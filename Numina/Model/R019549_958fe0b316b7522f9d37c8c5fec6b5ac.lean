import Mathlib

theorem inequalities_601610 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / 2 ≤ (x^2 + y * z) / (y + z)^2 + (y^2 + z * x) / (z + x)^2 +
    (z^2 + x * y) / (x + y)^2 := by

  have h1 : 0 < y + z := by linarith
  have h2 : 0 < z + x := by linarith
  have h3 : 0 < x + y := by linarith
  have h4 : (x^2 + y * z) / (y + z)^2 + (y^2 + z * x) / (z + x)^2 +
    (z^2 + x * y) / (x + y)^2 - 3 / 2 ≥ 0 := by
    have hx1 : 0 < (y + z) ^2 := by positivity
    have hx2 : 0 < (z + x) ^2 := by positivity
    have hx3 : 0 < (x + y) ^2 := by positivity
    have hx4 : 0 < (y + z) ^2 * (z + x) ^2 * (x + y) ^2 := by positivity
    have h4' : (x^2 + y * z) / (y + z)^2 + (y^2 + z * x) / (z + x) ^2 +
          (z^2 + x * y) / (x + y) ^2 - 3 / 2 =
        ( (x^2 + y * z) * (z + x) ^2 * (x + y) ^2 +
          (y^2 + z * x) * (y + z) ^2 * (x + y) ^2 +
          (z^2 + x * y) * (y + z) ^2 * (z + x) ^2 - 3 / 2 * (y + z) ^2 * (z + x) ^2 * (x + y) ^2 ) / ((y + z) ^2 * (z + x) ^2 * (x + y) ^2) := by 
      field_simp
      ring
    rw [h4']
    apply div_nonneg
    . nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
          mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)]
    . positivity
  linarith