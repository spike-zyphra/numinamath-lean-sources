import Mathlib

theorem inequalities_602686 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    3 ≤ 1/x^2 + 1/y^2 + 1/z^2 - 2*(x^3 + y^3 + z^3)/(x*y*z) := by
  have hx2 : x^2 > 0 := by nlinarith
  have hy2 : y^2 > 0 := by nlinarith
  have hz2 : z^2 > 0 := by nlinarith
  have hx3 : x^3 > 0 := by positivity
  have hy3 : y^3 > 0 := by positivity
  have hz3 : z^3 > 0 := by positivity
  have hxy : x * y > 0 := mul_pos hx hy
  have hxz : x * z > 0 := mul_pos hx hz
  have hyz : y * z > 0 := mul_pos hy hz
  have hxyz : x * y * z > 0 := by positivity
  have h2 : 1/x^2 + 1/y^2 + 1/z^2 - 2*(x^3 + y^3 + z^3)/(x*y*z) - 3 ≥ 0 := by
    have pos1 : 0 < x^2 * y^2 * z^2 := by positivity
    have eq1 : (1 / x^2 + 1 / y^2 + 1 / z^2 - 2 * (x^3 + y^3 + z^3) / (x * y * z) - 3) =
        (y^2 * z^2 + x^2 * z^2 + x^2 * y^2 - 2 * (x^3 + y^3 + z^3) * (x * y * z) - 3 * x^2 * y^2 * z^2) / (x^2 * y^2 * z^2):= by
      field_simp
      ring
    rw [eq1] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y * z), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      mul_pos (show 0 < x^2 by nlinarith) (show 0 < y^2 by nlinarith), 
      mul_pos (show 0 < y^2 by nlinarith) (show 0 < z^2 by nlinarith), 
      mul_pos (show 0 < x^2 by nlinarith) (show 0 < z^2 by nlinarith), 
      sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
      h
    ]
    positivity
  linarith