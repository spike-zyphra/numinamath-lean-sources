import Mathlib

theorem inequalities_597118 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / y + y / z + z / x ≤ y ^ 2 / x ^ 2 + z ^ 2 / y ^ 2 + x ^ 2 / z ^ 2 := by
  have hx2_pos : 0 < x^2 := by nlinarith
  have hy2_pos : 0 < y^2 := by nlinarith
  have hz2_pos : 0 < z^2 := by nlinarith
  have hx3_pos : 0 < x^3 := by nlinarith
  have hy3_pos : 0 < y^3 := by nlinarith
  have hz3_pos : 0 < z^3 := by nlinarith
  have h1 : 0 < x^2 * y^2 * z^2 := by positivity
  have h2 : x / y + y / z + z / x - (y ^ 2 / x ^ 2 + z ^ 2 / y ^ 2 + x ^ 2 / z ^ 2) ≤ 0 := by
    have h3 : x / y + y / z + z / x - (y ^ 2 / x ^ 2 + z ^ 2 / y ^ 2 + x ^ 2 / z ^ 2) =
        (x^3 * y * z^2 + x^2 * y^3 * z + x * y^2 * z^3 - (y^4 * z^2 + x^2 * z^4 + x^4 * y^2)) / (x^2 * y^2 * z^2) := by
      field_simp
      ring
    rw [h3]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      sq_nonneg (x^2 * y - y^2 * z), sq_nonneg (y^2 * z - z^2 * x), sq_nonneg (z^2 * x - x^2 * y), 
      sq_nonneg (x * y^2 - y * z^2), sq_nonneg (y * z^2 - z * x^2), sq_nonneg (z * x^2 - x * y^2), 
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos hx2_pos hy2_pos, mul_pos hx2_pos hz2_pos, mul_pos hy2_pos hz2_pos
    ]
    positivity
  linarith