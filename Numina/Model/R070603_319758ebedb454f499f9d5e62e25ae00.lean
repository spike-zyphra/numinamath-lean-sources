import Mathlib

theorem inequalities_58835 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / y + y / z + z / x ≥ z * (x + y) / (y * (y + z)) + x * (z + y) / (z * (x + z)) +
    y * (x + z) / (x * (x + y)) := by
  have pos1 : 0 < x * y := mul_pos hx hy
  have pos2 : 0 < y * z := mul_pos hy hz
  have pos3 : 0 < z * x := mul_pos hz hx
  have pos4 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  have pos5 : 0 < y * (y + z) := by positivity
  have pos6 : 0 < z * (x + z) := by positivity
  have pos7 : 0 < x * (x + y) := by positivity
  have h1 : x / y + y / z + z / x - (z * (x + y) / (y * (y + z)) + x * (z + y) / (z * (x + z)) + y * (x + z) / (x * (x + y))) ≥ 0 := by
    have h2 : x / y + y / z + z / x - (z * (x + y) / (y * (y + z)) + x * (z + y) / (z * (x + z)) + y * (x + z) / (x * (x + y))) =
      (x^2 * z * (x + y) * (y + z) * (x + z) + x * y^2 * (x + y) * (y + z) * (x + z) + y * z^2 * (x + y) * (y + z) * (x + z) - 
       (z * (x + y) * x * z * (x + y) * (x + z) + x * (z + y) * x * y * (x + y) * (y + z) + y * (x + z) * y * z * (y + z) * (x + z))) / 
      (x * y * z * (x + y) * (y + z) * (x + z)) := by
      field_simp
      ring
    rw [h2]
    have pos8 : 0 < x * y * z * (x + y) * (y + z) * (x + z) := by positivity
    have h3 : (x^2 * z * (x + y) * (y + z) * (x + z) + x * y^2 * (x + y) * (y + z) * (x + z) + y * z^2 * (x + y) * (y + z) * (x + z) - 
          (z * (x + y) * x * z * (x + y) * (x + z) + x * (z + y) * x * y * (x + y) * (y + z) + y * (x + z) * y * z * (y + z) * (x + z))) ≥ 0 := by 
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos hx hz, mul_pos hy hx, mul_pos hz hy
        ]
    apply div_nonneg h3 (by positivity)
  linarith