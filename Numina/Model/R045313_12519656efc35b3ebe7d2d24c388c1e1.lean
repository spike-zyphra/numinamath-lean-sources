import Mathlib

theorem inequalities_600330 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    x / (2 * x ^ 2 + y ^ 2 + z ^ 2) +
    y / (x ^ 2 + 2 * y ^ 2 + z ^ 2) +
    z / (x ^ 2 + y ^ 2 + 2 * z ^ 2) ≤ 9 / 4 := by 
  have h1 : 0 < (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2) := by positivity
  have h2 : x / (2 * x ^ 2 + y ^ 2 + z ^ 2) + y / (x ^ 2 + 2 * y ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2 + 2 * z ^ 2) - 9 / 4 ≤ 0 := by 
    have h3 : x / (2 * x ^ 2 + y ^ 2 + z ^ 2) + y / (x ^ 2 + 2 * y ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2 + 2 * z ^ 2) - 9 / 4 =
        ( (x * (x ^ 2 + 2 * y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2) ) +
          (y * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2) ) +
          (z * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) ) - (9 / 4) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2)
        ) / ( (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2) ) := by 
      field_simp
      ring
    rw [h3]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is non-positive
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
                sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
                sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
                sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
                h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    · -- Show the denominator is non-negative
      positivity
  linarith