import Mathlib

open Real

theorem inequalities_313 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    y ^ 2 / x ^ 2 + x ^ 2 / z ^ 2 + z ^ 2 / y ^ 2 ≥ y / x + x / z + z / y := by
  have hx2_pos : 0 < x ^ 2 := by
    positivity
  have hy2_pos : 0 < y ^ 2 := by
    positivity
  have hz2_pos : 0 < z ^ 2 := by
    positivity
  have h1 : y ^ 2 / x ^ 2 + x ^ 2 / z ^ 2 + z ^ 2 / y ^ 2 - (y / x + x / z + z / y) ≥ 0 := by 
    have h2 : y ^ 2 / x ^ 2 + x ^ 2 / z ^ 2 + z ^ 2 / y ^ 2 - (y / x + x / z + z / y) =
        (y ^ 4 * z ^ 2 + x ^ 4 * y ^ 2 + z ^ 4 * x ^ 2 - (x * y ^ 3 * z ^ 2 + x ^ 3 * y ^ 2 * z + x ^ 2 * y * z ^ 3)) / (x ^ 2 * y ^ 2 * z ^ 2) := by 
      field_simp 
      ring 
    rw [h2] at *
    apply div_nonneg 
    -- Prove the numerator is non-negative 
    nlinarith [sq_nonneg (y ^ 2 * z - x * y), sq_nonneg (x * y - x * z), sq_nonneg (x * z - y * y), 
            sq_nonneg (y ^ 2 * z - x ^ 2 * y), sq_nonneg (x ^ 2 * y - z ^ 2 * x), sq_nonneg (z ^ 2 * x - y ^ 2 * z), 
            sq_nonneg (y * x * z - x * y * y), sq_nonneg (y * x * z - x * x * z), sq_nonneg (y * x * z - y * y * z), 
            mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
            mul_pos (show 0 < x * z by nlinarith) (show 0 < y * z by nlinarith)]
    -- Prove the denominator is positive 
    positivity
  linarith