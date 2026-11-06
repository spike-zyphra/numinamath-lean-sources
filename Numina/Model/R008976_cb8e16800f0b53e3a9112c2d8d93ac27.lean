import Mathlib

theorem inequalities_45480 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + 2 * y) / (z + 2 * x + 3 * y) + (y + 2 * z) / (x + 2 * y + 3 * z) +
    (z + 2 * x) / (y + 2 * z + 3 * x) ≤ 3 / 2 := by
  have h1 : (x + 2 * y) / (z + 2 * x + 3 * y) + (y + 2 * z) / (x + 2 * y + 3 * z) + (z + 2 * x) / (y + 2 * z + 3 * x) - 3 / 2 ≤ 0 := by 
    have h1 : 0 < z + 2 * x + 3 * y := by positivity
    have h2 : 0 < x + 2 * y + 3 * z := by positivity
    have h3 : 0 < y + 2 * z + 3 * x := by positivity
    have h4 : (x + 2 * y) / (z + 2 * x + 3 * y) + (y + 2 * z) / (x + 2 * y + 3 * z) + (z + 2 * x) / (y + 2 * z + 3 * x) - 3 / 2 =
      ((x + 2 * y) * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) + (y + 2 * z) * (z + 2 * x + 3 * y) * (y + 2 * z + 3 * x) + (z + 2 * x) * (z + 2 * x + 3 * y) * (x + 2 * y + 3 * z) - 3 / 2 * (z + 2 * x + 3 * y) * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x)) / ((z + 2 * x + 3 * y) * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x)) := by 
      field_simp
      ring 
    rw [h4]
    apply div_nonpos_of_nonpos_of_nonneg 
    · -- Show that numerator is ≤ 0
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
    · -- Show that denominator is ≥ 0
      positivity
  linarith [h1]