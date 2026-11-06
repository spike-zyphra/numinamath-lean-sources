import Mathlib

theorem inequalities_603602 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by

  have hx2 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) ≥ 0 := by
    have h3 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) =
        (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^2 + y^2 + z^2) * (x * y * z)) / (x * y * z) := by 
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    -- Prove the inequality for the numerator
    have h4'1 : x^3 * y^2 + y^3 * z^2 + z^3 * x^2 ≥ (x^2 + y^2 + z^2) * (x * y * z) := by
      have h5 : 0 < x * y := by
        nlinarith
      have h6 : 0 < x * z := by
        nlinarith
      have h7 : 0 < y * z := by
        nlinarith
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith),
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ x * y by nlinarith),
          mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ z * x by nlinarith),
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ z by linarith),
          mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ y by linarith),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (y - z)), sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)), sq_nonneg (z * (y - z)), sq_nonneg (z * (x - y)),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    linarith
    all_goals
      positivity
  linarith [h2]