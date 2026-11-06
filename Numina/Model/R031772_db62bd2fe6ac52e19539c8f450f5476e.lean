import Mathlib

theorem inequalities_265088 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y ≥ x + y + z := by
  have h1 : 0 < x * y * z := by positivity
  have h2 : x * y * z = 1 := hxyz
  have h3 : 0 < x * y := by positivity
  have h4 : 0 < x * z := by positivity
  have h5 : 0 < y * z := by positivity
  have h6 : (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y - (x + y + z) ≥ 0 := by
    have h7 : 0 < x * y * z := by positivity
    have h9 : (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y - (x + y + z) =
          ((x + y - 1)^2 * (x * y) + (y + z - 1)^2 * (y * z) + (z + x - 1)^2 * (x * z) - (x + y + z) * (x * y * z)) / (x * y * z) := by
      field_simp
      <;> ring
    rw [h9] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
        sq_nonneg (x * (x - 1)), sq_nonneg (y * (y - 1)), sq_nonneg (z * (z - 1)),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, hxyz, sq_nonneg (x * y * z - 1)]
    all_goals positivity
  linarith [h6]