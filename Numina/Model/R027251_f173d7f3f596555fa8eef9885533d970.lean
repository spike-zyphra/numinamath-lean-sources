import Mathlib

theorem inequalities_31704 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y ≥ x ^ 2 + y ^ 2 + z ^ 2 := by
  have pos1 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  have h1 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by
    have h2 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) =
        (x^3 * y^2 + y^3 * z^2 + x^2 * z^3 - (x^3 * y * z + x * y^3 * z + x * y * z^3)) / (x * y * z) := by
      field_simp
      ring
    rw [h2] at *
    have h3 : (x^3 * y^2 + y^3 * z^2 + x^2 * z^3 - (x^3 * y * z + x * y^3 * z + x * y * z^3)) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (y - z)), sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)), sq_nonneg (z * (y - z)), sq_nonneg (z * (x - y)), 
            mul_nonneg (show (0 : ℝ) ≤ x - y by linarith) (show (0 : ℝ) ≤ y - z by linarith), 
              mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y - z by linarith), 
                mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ x - y by linarith), 
                  mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
                  ]
    apply div_nonneg 
    linarith [h3]
    positivity 
  linarith [h1]