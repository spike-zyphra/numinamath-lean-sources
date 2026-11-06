import Mathlib

theorem inequalities_211077 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y * z / (x ^ 3 + y ^ 3 + x * y * z) +
    y * z * x / (y ^ 3 + z ^ 3 + y * z * x) +
    z * x * y / (z ^ 3 + x ^ 3 + z * x * y) ≤ 1 := by

  have h1 : x ^ 3 + y ^ 3 ≥ x^2 * y + x * y^2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy]

  have h2 : y ^ 3 + z ^ 3 ≥ y^2 * z + y * z^2 := by
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), mul_pos hy hz]

  have h3 : z ^ 3 + x ^ 3 ≥ z^2 * x + z * x^2 := by
    nlinarith [sq_nonneg (z - x), sq_nonneg (z + x), mul_pos hz hx]

  have h4 : x ^ 3 + y ^ 3 + x * y * z ≥ x * y * (x + y + z) := by
    nlinarith [h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h4' : y ^ 3 + z ^ 3 + y * z * x ≥ y * z * (x + y + z) := by 
    nlinarith [h2, mul_pos hy hz, mul_pos hy hx, mul_pos hz hx]

  have h4'' : z ^ 3 + x ^ 3 + z * x * y ≥ z * x * (x + y + z) := by 
    nlinarith [h3, mul_pos hz hx, mul_pos hz hy, mul_pos hx hy]

  have h5 : x * y * z / (x ^ 3 + y ^ 3 + x * y * z) ≤ z / (x + y + z) := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h4]

  have h6 : y * z * x / (y ^ 3 + z ^ 3 + y * z * x) ≤ x / (x + y + z) := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [mul_pos hy hz, mul_pos hx hy, mul_pos hx hz, h4']

  have h7 : z * x * y / (z ^ 3 + x ^ 3 + z * x * y) ≤ y / (x + y + z) := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [mul_pos hz hx, mul_pos hx hy, mul_pos hz hy, h4'']

  have h8 : x * y * z / (x ^ 3 + y ^ 3 + x * y * z) + y * z * x / (y ^ 3 + z ^ 3 + y * z * x) + z * x * y / (z ^ 3 + x ^ 3 + z * x * y) ≤ (z / (x + y + z) + x / (x + y + z) + y / (x + y + z)) := by
    linarith [h5, h6, h7]

  have h9 : (z / (x + y + z) + x / (x + y + z) + y / (x + y + z)) = 1 := by
    field_simp
    <;> ring

  linarith [h8, h9]