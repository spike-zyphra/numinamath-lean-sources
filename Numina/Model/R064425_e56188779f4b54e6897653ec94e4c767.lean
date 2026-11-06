import Mathlib

theorem inequalities_672 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
  y * z * (y + z) / x + z * x * (z + x) / y + x * y * (x + y) / z ≥
  1 / 2 * (y + z)^2 + 1 / 2 * (z + x)^2 + 1 / 2 * (x + y)^2 +
  3 / 4 * x * (1 / y + 1 / z) * (y - z)^2 := by
  have pos1 : 0 < x * y := by nlinarith
  have pos2 : 0 < x * z := by nlinarith
  have pos3 : 0 < y * z := by nlinarith
  have pos4 : 0 < x * y * z := by positivity

  have h1 : y * z * (y + z) / x + z * x * (z + x) / y + x * y * (x + y) / z - (1 / 2 * (y + z)^2 + 1 / 2 * (z + x)^2 + 1 / 2 * (x + y)^2 + 3 / 4 * x * (1 / y + 1 / z) * (y - z)^2) ≥ 0 := by
    have h2 : y * z * (y + z) / x + z * x * (z + x) / y + x * y * (x + y) / z - (1 / 2 * (y + z)^2 + 1 / 2 * (z + x)^2 + 1 / 2 * (x + y)^2 + 3 / 4 * x * (1 / y + 1 / z) * (y - z)^2) =
      (y^2 * z^2 * (y + z) + x^2 * z^2 * (z + x) + x^2 * y^2 * (x + y) - 1 / 2 * (x * y * z) * ((y + z)^2 + (z + x)^2 + (x + y)^2) - 3 / 4 * x^2 * (y + z) * (y - z)^2) / (x * y * z) := by
      field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz]
      ring
    rw [h2]
    have h3 : (y^2 * z^2 * (y + z) + x^2 * z^2 * (z + x) + x^2 * y^2 * (x + y) - 1 / 2 * (x * y * z) * ((y + z)^2 + (z + x)^2 + (x + y)^2) - 3 / 4 * x^2 * (y + z) * (y - z)^2) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - x * z), sq_nonneg (y * x - y * z), sq_nonneg (z * x - z * y),
        sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (z * (x - y)),
        sq_nonneg (x * y + x * z - 2 * y * z), 
        sq_nonneg (x * y - x * z), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    apply div_nonneg h3 (by positivity)

  linarith