import Mathlib

theorem inequalities_143093 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 ≥ x / y + y / z + z / x := by
  have h2 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 - (x / y + y / z + z / x) ≥ 0 := by
    have hx' : 0 < x := hx
    have hy' : 0 < y := hy
    have hz' : 0 < z := hz
    have h3 : 0 < x^2 * y^2 * z^2 := by positivity
    have h4 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 - (x / y + y / z + z / x) =
      (x^4 * z^2 + y^4 * x^2 + z^4 * y^2 - (x^3 * y * z^2 + x^2 * y^3 * z + x * y^2 * z^3)) / (x^2 * y^2 * z^2) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x^2 * z - y^2 * x), sq_nonneg (y^2 * x - z^2 * y), sq_nonneg (z^2 * y - x^2 * z), 
          sq_nonneg (x * z - y * x), sq_nonneg (y * x - z * y), sq_nonneg (z * y - x * z), 
          sq_nonneg (x * (x * z - y * x)), sq_nonneg (y * (y * x - z * y)), sq_nonneg (z * (z * y - x * z)), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
          mul_pos (show 0 < x * y by positivity) (show 0 < y * z by positivity), 
          mul_pos (show 0 < y * z by positivity) (show 0 < x * z by positivity), 
          mul_pos (show 0 < x * y by positivity) (show 0 < x * z by positivity)]
    all_goals positivity
  linarith