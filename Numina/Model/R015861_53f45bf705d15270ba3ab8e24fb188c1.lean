import Mathlib

theorem inequalities_600624 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y ≥ x ^ 2 + y ^ 2 + z ^ 2 := by 
  have hx' : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h1 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by
    have hx_pos : 0 < x := hx
    have hy_pos : 0 < y := hy
    have hz_pos : 0 < z := hz
    have h2 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) =
        (x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2 + z ^ 3 * x ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z)) / (x * y * z) := by 
      field_simp
      ring
    rw [h2] at *
    have h3 : x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2 + z ^ 3 * x ^ 2 ≥ (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z) := by 
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (y - z)), sq_nonneg (z * (y - z)), 
          sq_nonneg (z * (x - y)), sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)), 
          mul_pos hx hy, mul_pos hx hz, 
          mul_pos hy hz, 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith), 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ z by linarith)
      ]
    have h4 : x * y * z > 0 := by positivity
    apply div_nonneg
    linarith [h3]
    all_goals linarith [h4]

  linarith [h1]