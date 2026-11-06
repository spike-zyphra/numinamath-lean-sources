import Mathlib

theorem inequalities_120662 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / y + y / z + z / x + x / z + z / y + y / x ≥ 6 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h34 : (x^2 * z) + (y^2 * x) + (z^2 * y) + (x^2 * y) + (z^2 * x) + (y^2 * z) - 6 * (x * y * z) ≥ 0 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos hx hz
      ]
  have h3 : (x / y + y / z + z / x + x / z + z / y + y / x - 6) =
           ( (x^2 * z) + (y^2 * x) + (z^2 * y) + (x^2 * y) + (z^2 * x) + (y^2 * z) - 6 * (x * y * z) ) / (x * y * z) := by
    field_simp
    ring
  have h20 : ( (x^2 * z) + (y^2 * x) + (z^2 * y) + (x^2 * y) + (z^2 * x) + (y^2 * z) - 6 * (x * y * z) ) / (x * y * z) ≥ 0 := by
    apply div_nonneg
    linarith
    all_goals positivity
  linarith [h3, h20]
  all_goals linarith