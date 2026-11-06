import Mathlib

theorem inequalities_320646 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by 
  have pos1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h1 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) ≥ 0 := by
    have h2 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) =
          (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^2 + y^2 + z^2) * (x * y * z)) / (x * y * z) := by
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      ring
    rw [h2]
    have h3 : x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^2 + y^2 + z^2) * (x * y * z) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_nonneg (show 0 ≤ x - z by linarith) (show 0 ≤ (x - y) * (y - z) by nlinarith),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    apply div_nonneg h3 (by positivity)
  
  linarith