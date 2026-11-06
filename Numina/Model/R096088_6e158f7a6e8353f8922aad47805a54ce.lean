import Mathlib

theorem inequalities_110749 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / y + y / z + z / x + x / z + z / y + y / x ≥ 6 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : x / y + y / z + z / x + x / z + z / y + y / x - 6 ≥ 0 := by
    have h3 : x / y + y / z + z / x + x / z + z / y + y / x - 6 =
      (x^2*z + x*y^2 + y*z^2 + x^2*y + x*z^2 + y^2*z - 6*x*y*z) / (x*y*z) := by
      field_simp
      ring_nf
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (x*y - y*z), sq_nonneg (y*z - x*z), sq_nonneg (x*y - z*x),
      sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x*z - y*x), sq_nonneg (x*y - y*z), sq_nonneg (y*z - x*z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    positivity
  linarith