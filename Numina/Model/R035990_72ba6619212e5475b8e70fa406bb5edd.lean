import Mathlib

theorem inequalities_126230 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    6 ≤ x / y + y / z + z / x + y / x + z / y + x / z := by 
  have h1 : x / y + y / x ≥ 2 := by 
    have h2 : x * y > 0 := mul_pos hx hy
    have h3 : x / y + y / x - 2 ≥ 0 := by
      have h4 : x / y + y / x - 2 = (x^2 + y^2 - 2 * x * y) / (x * y) := by
        field_simp
        <;> ring
      rw [h4]
      have h5 : x^2 + y^2 - 2 * x * y = (x - y) ^2 := by 
        ring
      rw [h5]
      apply div_nonneg 
      linarith [show 0 ≤ (x - y) ^ 2 by positivity]
      positivity 
    linarith
  have h2 : y / z + z / y ≥ 2 := by 
    have h3 : y * z > 0 := mul_pos hy hz
    have h4 : y / z + z / y - 2 ≥ 0 := by
      have h5 : y / z + z / y - 2 = (y^2 + z^2 - 2 * y * z) / (y * z) := by
        field_simp
        <;> ring
      rw [h5]
      have h6 : y^2 + z^2 - 2 * y * z = (y - z) ^2 := by 
        ring
      rw [h6]
      apply div_nonneg 
      linarith [show 0 ≤ (y - z) ^ 2 by positivity]
      positivity 
    linarith
  have h3 : z / x + x / z ≥ 2 := by 
    have h4 : z * x > 0 := mul_pos hz hx
    have h5 : z / x + x / z - 2 ≥ 0 := by
      have h6 : z / x + x / z - 2 = (z^2 + x^2 - 2 * z * x) / (z * x) := by
        field_simp
        <;> ring
      rw [h6]
      have h7 : z^2 + x^2 - 2 * z * x = (z - x) ^2 := by 
        ring
      rw [h7]
      apply div_nonneg 
      linarith [show 0 ≤ (z - x) ^ 2 by positivity]
      positivity 
    linarith
  linarith [h1, h2, h3]