import Mathlib

theorem inequalities_319941 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by
  have h1 : x * y * z > 0 := by positivity
  have h2 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) ≥ 0 := by
    have h3 : x * y * z > 0 := by positivity
    have h4 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) =
        (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x * y * z) * (x^2 + y^2 + z^2)) / (x * y * z) := by
      field_simp
      ring
    rw [h4]
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y) + y * (y - z) + z * (z - x)), 
      sq_nonneg (x * (x - z) + y * (y - z) + z * (z - x)), 
      sq_nonneg (x * (x - y) + y * (y - x) + z * (z - x)), 
      mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith),
      mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ z by linarith),
      mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ z by linarith),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
    all_goals positivity
  linarith
  all_goals try positivity
  all_goals try nlinarith