import Mathlib

theorem inequalities_604801 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
  x^3 / (y^2 + z^2) + y^3 / (z^2 + x^2) + z^3 / (x^2 + y^2) ≥
  (x + y + z) / 2 := by
  have hx2 : 0 < x^2 := by nlinarith
  have hy2 : 0 < y^2 := by nlinarith
  have hz2 : 0 < z^2 := by nlinarith

  have h1 : 0 < y^2 + z^2 := by
    nlinarith [sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h2 : 0 < z^2 + x^2 := by
    nlinarith [sq_pos_of_pos hz, sq_pos_of_pos hx]

  have h3 : 0 < x^2 + y^2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]

  have h4 : x^3 / (y^2 + z^2) + y^3 / (z^2 + x^2) + z^3 / (x^2 + y^2) - (x + y + z) / 2 ≥ 0 := by
    have h5 : x^3 / (y^2 + z^2) + y^3 / (z^2 + x^2) + z^3 / (x^2 + y^2) - (x + y + z) / 2 =
        (x^3 * (z^2 + x^2) * (x^2 + y^2) + y^3 * (y^2 + z^2) * (x^2 + y^2) + z^3 * (y^2 + z^2) * (z^2 + x^2) - (x + y + z) / 2 * (y^2 + z^2) * (z^2 + x^2) * (x^2 + y^2)) / ((y^2 + z^2) * (z^2 + x^2) * (x^2 + y^2)) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    · -- Prove the numerator is non-negative
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2), 
          sq_nonneg (x * y - y * z), sq_nonneg (x * y - z * x), sq_nonneg (y * z - z * x), 
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
          mul_pos hx (show 0 < x^2 by positivity), 
          mul_pos hx (show 0 < y^2 by positivity), 
          mul_pos hx (show 0 < z^2 by positivity), 
          mul_pos hy (show 0 < x^2 by positivity), 
          mul_pos hy (show 0 < y^2 by positivity), 
          mul_pos hy (show 0 < z^2 by positivity), 
          mul_pos hz (show 0 < x^2 by positivity), 
          mul_pos hz (show 0 < y^2 by positivity), 
          mul_pos hz (show 0 < z^2 by positivity)
        ]
    all_goals
      positivity
  linarith