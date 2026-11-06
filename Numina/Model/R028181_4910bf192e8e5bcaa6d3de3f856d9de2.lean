import Mathlib

theorem inequalities_290586 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y / (x ^ 2 + y ^ 2 + 2 * z ^ 2)) +
    (y * z / (2 * x ^ 2 + y ^ 2 + z ^ 2)) +
    (z * x / (x ^ 2 + 2 * y ^ 2 + z ^ 2)) ≤ 3 / 4 := by

  have h1 : (x * y / (x ^ 2 + y ^ 2 + 2 * z ^ 2)) +
    (y * z / (2 * x ^ 2 + y ^ 2 + z ^ 2)) +
      (z * x / (x ^ 2 + 2 * y ^ 2 + z ^ 2)) - 3 / 4 ≤ 0 := by
    have hx1 : 0 < x ^ 2 + y ^ 2 + 2 * z ^ 2 := by positivity
    have hx2 : 0 < 2 * x ^ 2 + y ^ 2 + z ^ 2 := by positivity
    have hx3 : 0 < x ^ 2 + 2 * y ^ 2 + z ^ 2 := by positivity
    have h4 : (x * y / (x ^ 2 + y ^ 2 + 2 * z ^ 2)) +
      (y * z / (2 * x ^ 2 + y ^ 2 + z ^ 2)) +
      (z * x / (x ^ 2 + 2 * y ^ 2 + z ^ 2)) - 3 / 4 =
        (x * y * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) + 
              y * z * (x ^ 2 + y ^ 2 + 2 * z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) + 
              z * x * (x ^ 2 + y ^ 2 + 2 * z ^ 2) * (2 * x ^ 2 + y ^ 2 + z ^ 2) - 
              3 / 4 * (x ^ 2 + y ^ 2 + 2 * z ^ 2) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2)
        ) / ((x ^ 2 + y ^ 2 + 2 * z ^ 2) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2)) := by
      field_simp
      ring
    rw [h4] at *
    have pos1 : (x ^ 2 + y ^ 2 + 2 * z ^ 2) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) > 0 := by positivity
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (x * (y - z)), 
          sq_nonneg (y * (x - y)), sq_nonneg (y * (x - z)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (x - y)), sq_nonneg (z * (x - z)), sq_nonneg (z * (y - z)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
          mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)
        ]
    all_goals positivity
  linarith