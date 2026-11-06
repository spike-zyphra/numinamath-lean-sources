import Mathlib

theorem inequalities_597142 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z ≥ 1) :
    (y + z) / x + (z + x) / y + (x + y) / z ≥ 2 * (1 / x + 1 / y + 1 / z) := by

  have h1 : (y + z) / x + (z + x) / y + (x + y) / z - 2 * (1 / x + 1 / y + 1 / z) ≥ 0 := by
    have h2 : (y + z) / x + (z + x) / y + (x + y) / z - 2 * (1 / x + 1 / y + 1 / z) =
        ((y + z) * y * z + (z + x) * x * z + (x + y) * x * y - 2 * (y * z + x * z + x * y)) / (x * y * z) := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, hxyz,
        mul_pos (show (0 : ℝ) < x * y from by positivity) (show (0 : ℝ) < x * y * z from by positivity)
      ]
    positivity
  linarith