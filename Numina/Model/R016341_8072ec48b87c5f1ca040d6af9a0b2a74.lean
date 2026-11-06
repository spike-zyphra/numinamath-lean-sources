import Mathlib

theorem inequalities_8806 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y ≥ x ^ 2 + y ^ 2 + z ^ 2 := by
  have h2 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by
    have hx1 : x > 0 := hx
    have hy1 : y > 0 := hy
    have hz1 : z > 0 := hz
    have hx2 : 0 < x * y * z := by positivity
    have h4 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) =
        (x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2 + z ^ 3 * x ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z)) / (x * y * z) := by
      field_simp
      ring
    rw [h4]
    have h5 : x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2 + z ^ 3 * x ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith), 
          mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ x * y by nlinarith), 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y * (y - z) by nlinarith), 
          mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ (y - z) by linarith), 
          mul_nonneg (show 0 ≤ (y ^ 2 - z ^ 2) by nlinarith) (show 0 ≤ (x - y) by linarith), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith),
          sq_nonneg (x * y - x * z), sq_nonneg (x * y - z * x), sq_nonneg (y * z - x * z)
        ]
    have h9 : (x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2 + z ^ 3 * x ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z)) / (x * y * z) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith [h2]