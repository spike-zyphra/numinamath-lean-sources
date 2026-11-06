import Mathlib

theorem inequalities_230505 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (y + z) + y / (z + x) + z / (x + y) ≥ 3 / 2 := by
  have h1 : 0 < y * z := mul_pos hy hz
  have h2 : 0 < z * x := mul_pos hz hx
  have h3 : 0 < x * y := mul_pos hx hy
  have h4 : 0 < (y + z) * (z + x) * (x + y) := by
    positivity
  have h5 : x / (y + z) + y / (z + x) + z / (x + y) - 3 / 2 ≥ 0 := by
    have pos1 : y + z > 0 := by linarith
    have pos2 : z + x > 0 := by linarith
    have pos3 : x + y > 0 := by linarith
    have pos4 : (y + z) * (z + x) * (x + y) > 0 := by positivity
    have h6 : x / (y + z) + y / (z + x) + z / (x + y) - 3 / 2 =
        (x * (z + x) * (x + y) + y * (y + z) * (x + y) + z * (y + z) * (z + x) - 3 / 2 * (y + z) * (z + x) * (x + y)) / ((y + z) * (z + x) * (x + y)) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
              sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
              sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
              mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith),
              mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith),
              mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)
            ]
    positivity
  linarith