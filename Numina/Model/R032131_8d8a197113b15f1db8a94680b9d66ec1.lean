import Mathlib

theorem inequalities_1168 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 * (x + y) * (y + z) * (z + x) ≥ x * y * (2 * x + y + z) * (2 * y + z + x) / (x + y) +
    y * z * (2 * y + z + x) * (2 * z + x + y) / (y + z) + z * x * (2 * z + x + y) * (2 * x + y + z) / (z + x) := by
  have hx1 : 0 < x + y := by linarith
  have hy1 : 0 < y + z := by linarith
  have hz1 : 0 < z + x := by linarith
  have h1 : 0 < (x + y) * (y + z) * (z + x) := by positivity
  have h4 : x * y * (2 * x + y + z) * (2 * y + z + x) / (x + y) + 
    y * z * (2 * y + z + x) * (2 * z + x + y) / (y + z) + 
    z * x * (2 * z + x + y) * (2 * x + y + z) / (z + x) - 3 * (x + y) * (y + z) * (z + x) ≤ 0 := by
    have hx2 : 0 < x + y := by nlinarith
    have hy2 : 0 < y + z := by nlinarith
    have hz2 : 0 < z + x := by nlinarith
    have h3 : 0 < (x + y) * (y + z) * (z + x) := by positivity
    have h5 : x * y * (2 * x + y + z) * (2 * y + z + x) / (x + y) + y * z * (2 * y + z + x) * (2 * z + x + y) / (y + z) + z * x * (2 * z + x + y) * (2 * x + y + z) / (z + x) - 3 * (x + y) * (y + z) * (z + x) = 
        (x * y * (2 * x + y + z) * (2 * y + z + x) * (y + z) * (z + x) + y * z * (2 * y + z + x) * (2 * z + x + y) * (x + y) * (z + x) + z * x * (2 * z + x + y) * (2 * x + y + z) * (x + y) * (y + z) - 3 * (x + y) * (y + z) * (z + x) * ((x + y) * (y + z) * (z + x)) ) / ((x + y) * (y + z) * (z + x)) := by 
      field_simp
      ring
    rw [h5] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is non-positive
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos hx hz, mul_pos hy hx, mul_pos hz hy
        ]
    · -- Show the denominator is non-negative
      positivity
  linarith