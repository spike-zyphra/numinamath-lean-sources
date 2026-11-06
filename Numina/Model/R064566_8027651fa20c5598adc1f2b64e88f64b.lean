import Mathlib

theorem inequalities_597568 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^2 / ((2 * x + y) * (2 * x + z)) + y^2 / ((2 * y + z) * (2 * y + x)) +
    z^2 / ((2 * z + x) * (2 * z + y)) ≤ 1 / 3 := by
  have hx2 : 0 < 2 * x + y := by linarith
  have hx3 : 0 < 2 * x + z := by linarith
  have hy2 : 0 < 2 * y + z := by linarith
  have hy3 : 0 < 2 * y + x := by linarith
  have hz2 : 0 < 2 * z + x := by linarith
  have hz3 : 0 < 2 * z + y := by linarith
  have hxy : 0 < (2 * x + y) * (2 * x + z) * (2 * y + z) * (2 * y + x) * (2 * z + x) * (2 * z + y) := by positivity
  have h1 : x^2 / ((2 * x + y) * (2 * x + z)) + y^2 / ((2 * y + z) * (2 * y + x)) +
    z^2 / ((2 * z + x) * (2 * z + y)) - 1 / 3 ≤ 0 := by
    have h2 : x^2 / ((2 * x + y) * (2 * x + z)) + y^2 / ((2 * y + z) * (2 * y + x)) +
      z^2 / ((2 * z + x) * (2 * z + y)) - 1 / 3 =
      (x^2 * 3 * (2 * y + z) * (2 * y + x) * (2 * z + x) * (2 * z + y) +
       y^2 * 3 * (2 * x + y) * (2 * x + z) * (2 * z + x) * (2 * z + y) +
       z^2 * 3 * (2 * x + y) * (2 * x + z) * (2 * y + z) * (2 * y + x) -
       (2 * x + y) * (2 * x + z) * (2 * y + z) * (2 * y + x) * (2 * z + x) * (2 * z + y)) /
      (3 * (2 * x + y) * (2 * x + z) * (2 * y + z) * (2 * y + x) * (2 * z + x) * (2 * z + y)) := by
      field_simp
      ring
    rw [h2]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
      sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
      sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    positivity
  linarith