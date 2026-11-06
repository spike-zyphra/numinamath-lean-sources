import Mathlib

theorem inequalities_302660 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by
  have hx_pos : 0 < x := hx
  have hy_pos : 0 < y := hy
  have hz_pos : 0 < z := hz
  have h1 : 0 < x * y * z := by
    positivity
  suffices x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x^2 + y^2 + z^2) ≥ 0 by linarith
  have h2 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x^2 + y^2 + z^2) =
    (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^2 + y^2 + z^2) * (x * y * z)) / (x * y * z) := by
    field_simp
    ring
  rw [h2]
  apply div_nonneg
  -- We need to show that the numerator is non-negative
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
    sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
    sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
    mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
    mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - z by linarith),
    mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ x - y by linarith),
    mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ y - z by linarith)]
  all_goals
    positivity