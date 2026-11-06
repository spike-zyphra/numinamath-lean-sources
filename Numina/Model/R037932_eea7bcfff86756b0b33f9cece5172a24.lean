import Mathlib

theorem inequalities_599170 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    (x^2 * y) / z + (y^2 * z) / x + (z^2 * x) / y ≥ x^2 + y^2 + z^2 := by
  have hx6 : 0 < x := hx
  have hy6 : 0 < y := hy
  have hz6 : 0 < z := hz
  have h2 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h3 : (x^2 * y) / z + (y^2 * z) / x + (z^2 * x) / y - (x^2 + y^2 + z^2) ≥ 0 := by
    have hx_pos : 0 < x := hx
    have hy_pos : 0 < y := hy
    have hz_pos : 0 < z := hz
    have hx6 : 0 < x := hx
    have hy6 : 0 < y := hy
    have hz6 : 0 < z := hz
    have h4 : (x^2 * y) / z + (y^2 * z) / x + (z^2 * x) / y - (x^2 + y^2 + z^2) =
        (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^2 + y^2 + z^2)*(x*y*z)) / (x*y*z) := by 
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    have h5 : x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2 + z ^ 3 * x ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z) ≥ 0 := by
      have hx12 : x - y ≥ 0 := by linarith
      have hy12 : y - z ≥ 0 := by linarith
      have hx2 : z > 0 := hz
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        mul_nonneg (show (0 : ℝ) ≤ x - y by linarith) (show (0 : ℝ) ≤ y - z by linarith), 
        mul_nonneg (show (0 : ℝ) ≤ x - y by linarith) (show (0 : ℝ) ≤ z by linarith),
        mul_nonneg (show (0 : ℝ) ≤ y - z by linarith) (show (0 : ℝ) ≤ z by linarith), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    linarith
    positivity

  linarith