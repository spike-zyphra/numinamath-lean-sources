import Mathlib

theorem inequalities_217640 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    2 ≤ (x ^ 3 + y ^ 3) / (x ^ 2 + x * y + y ^ 2) +
        (y ^ 3 + z ^ 3) / (y ^ 2 + y * z + z ^ 2) +
        (z ^ 3 + x ^ 3) / (z ^ 2 + z * x + x ^ 2) := by
  have h10 : (x ^ 3 + y ^ 3) / (x ^ 2 + x * y + y ^ 2) ≥ (x + y) / 3 := by 
    have h1 : 0 < x ^ 2 + x * y + y ^ 2 := by
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x - y), sq_nonneg (x * y)]
    have h2 : (x ^ 3 + y ^ 3) ≥ (x + y) / 3 * (x ^ 2 + x * y + y ^ 2) := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), mul_pos hx hy, sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), sq_nonneg (x * y)]
    have h3 : (x ^ 3 + y ^ 3) / (x ^ 2 + x * y + y ^ 2) ≥ (x + y) / 3 := by 
      apply (le_div_iff₀ h1).mpr 
      linarith [h2]
    exact h3
  have h11 : (y ^ 3 + z ^ 3) / (y ^ 2 + y * z + z ^ 2) ≥ (y + z) / 3 := by 
    have h1 : 0 < y ^ 2 + y * z + z ^ 2 := by
      nlinarith [sq_pos_of_pos hy, sq_pos_of_pos hz, sq_nonneg (y - z), sq_nonneg (y * z)]
    have h2 : (y ^ 3 + z ^ 3) ≥ (y + z) / 3 * (y ^ 2 + y * z + z ^ 2) := by 
      nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), sq_nonneg (y^2 - z^2), mul_pos hy hz, sq_nonneg (y * (y - z)), sq_nonneg (z * (y - z)), sq_nonneg (y * z)]
    have h3 : (y ^ 3 + z ^ 3) / (y ^ 2 + y * z + z ^ 2) ≥ (y + z) / 3 := by 
      apply (le_div_iff₀ h1).mpr 
      linarith [h2]
    exact h3
  have h12 : (z ^ 3 + x ^ 3) / (z ^ 2 + z * x + x ^ 2) ≥ (z + x) / 3 := by 
    have h1 : 0 < z ^ 2 + z * x + x ^ 2 := by
      nlinarith [sq_pos_of_pos hz, sq_pos_of_pos hx, sq_nonneg (z - x), sq_nonneg (z * x)]
    have h2 : (z ^ 3 + x ^ 3) ≥ (z + x) / 3 * (z ^ 2 + z * x + x ^ 2) := by 
      nlinarith [sq_nonneg (z - x), sq_nonneg (z + x), sq_nonneg (z^2 - x^2), mul_pos hz hx, sq_nonneg (z * (z - x)), sq_nonneg (x * (z - x)), sq_nonneg (z * x)]
    have h3 : (z ^ 3 + x ^ 3) / (z ^ 2 + z * x + x ^ 2) ≥ (z + x) / 3 := by 
      apply (le_div_iff₀ h1).mpr 
      linarith [h2]
    exact h3
  have h13 : x + y + z ≥ 3 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
  have h14 : (x ^ 3 + y ^ 3) / (x ^ 2 + x * y + y ^ 2) + (y ^ 3 + z ^ 3) / (y ^ 2 + y * z + z ^ 2) + (z ^ 3 + x ^ 3) / (z ^ 2 + z * x + x ^ 2) ≥ 2 * (x + y + z) / 3 := by 
    linarith [h10, h11, h12]
  linarith [h14, h13]