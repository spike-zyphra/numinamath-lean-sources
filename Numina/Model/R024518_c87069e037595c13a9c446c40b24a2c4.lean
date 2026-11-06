import Mathlib

theorem inequalities_599071 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by

  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by
    have h3 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) =
        (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^3 * y * z + y^3 * x * z + z^3 * x * y)) / (x * y * z) := by
      field_simp
      ring
    rw [h3]
    have h3_pos : x * y * z > 0 := h1
    have h4 : x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^3 * y * z + y^3 * x * z + z^3 * x * y) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        sq_nonneg (x * (y - x)), sq_nonneg (y * (z - y)), sq_nonneg (z * (x - z)), 
        mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith), 
        mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ z by linarith), 
        mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ z by linarith), 
        mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
        sq_nonneg (x * (x - y)), sq_nonneg (y * (y - z)), 
        mul_nonneg (show 0 ≤ (x - y : ℝ) by linarith) (show 0 ≤ (y - z : ℝ) by linarith)
      ]
    apply div_nonneg 
    linarith 
    all_goals nlinarith 
  linarith