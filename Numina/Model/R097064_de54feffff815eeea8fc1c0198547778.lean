import Mathlib

theorem inequalities_74202 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (y + z) + 25 * y / (z + x) + 4 * z / (x + y) > 2 := by
  have h1 : 0 < y + z := by nlinarith
  have h2 : 0 < z + x := by nlinarith
  have h3 : 0 < x + y := by nlinarith

  have h4 : x / (y + z) + 25 * y / (z + x) + 4 * z / (x + y) - 2 > 0 := by
    have h5 : x / (y + z) + 25 * y / (z + x) + 4 * z / (x + y) - 2 =
      (x * (z + x) * (x + y) + 25 * y * (y + z) * (x + y) + 4 * z * (y + z) * (z + x) - 2 * (y + z) * (z + x) * (x + y)) / ((y + z) * (z + x) * (x + y)) := by
      field_simp
      <;> ring

    rw [h5]

    have h6 : (y + z) * (z + x) * (x + y) > 0 := by positivity

    have h7 : x * (z + x) * (x + y) + 25 * y * (y + z) * (x + y) + 4 * z * (y + z) * (z + x) - 2 * (y + z) * (z + x) * (x + y) > 0 := by
      nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y - 2 * z), sq_nonneg (z - 2 * x),
                sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

    apply div_pos h7 (by positivity)

  linarith