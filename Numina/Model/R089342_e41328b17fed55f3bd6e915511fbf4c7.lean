import Mathlib

theorem inequalities_302571 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 / 4 := by 
  have h1 : 2 * x + y + z > 0 := by positivity
  have h2 : x + 2 * y + z > 0 := by positivity
  have h3 : x + y + 2 * z > 0 := by positivity
  have h4 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ≤ 0 := by
    have pos1 : (2 * x + y + z) > 0 := h1
    have pos2 : (x + 2 * y + z) > 0 := h2
    have pos3 : (x + y + 2 * z) > 0 := h3
    have h5 : (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) > 0 := by positivity
    have h6 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 =
      (x * (x + 2 * y + z) * (x + y + 2 * z) + y * (2 * x + y + z) * (x + y + 2 * z) + z * (2 * x + y + z) * (x + 2 * y + z) - (3 / 4) * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by
      field_simp
      ring
    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- need to prove numerator ≤ 0
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    · -- need to prove denominator ≥ 0
      positivity
  linarith