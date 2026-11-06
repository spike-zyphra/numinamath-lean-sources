import Mathlib

theorem inequalities_603706 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 / 4 := by
  have pos1 : 0 < (2 * x + y + z) := by positivity
  have pos2 : 0 < (x + 2 * y + z) := by positivity
  have pos3 : 0 < (x + y + 2 * z) := by positivity
  have h4 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ≤ 0 := by
    have pos1 : 0 < (2 * x + y + z) := by positivity
    have pos2 : 0 < (x + 2 * y + z) := by positivity
    have pos3 : 0 < (x + y + 2 * z) := by positivity
    have h4 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 =
        ( (x * (x + 2 * y + z) * (x + y + 2 * z) ) +
          (y * (2 * x + y + z) * (x + y + 2 * z) ) +
          (z * (2 * x + y + z) * (x + 2 * y + z) ) - 3 / 4 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) ) / ( (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) ) := by
      field_simp
      ring
    rw [h4]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is less than or equal to zero.
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    · -- Show that the denominator is ≥ 0.
      positivity
  linarith