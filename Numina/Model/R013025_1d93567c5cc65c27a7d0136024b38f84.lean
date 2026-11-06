import Mathlib

theorem inequalities_597414 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y * z / (2 * x ^ 2 + y ^ 2 + z ^ 2)) +
    (z * x / (2 * y ^ 2 + z ^ 2 + x ^ 2)) +
    (x * y / (2 * z ^ 2 + x ^ 2 + y ^ 2)) ≤ 3 / 4 := by
  have h1 : 0 < 2 * x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h2 : 0 < 2 * y ^ 2 + z ^ 2 + x ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h3 : 0 < 2 * z ^ 2 + x ^ 2 + y ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h4 : (y * z / (2 * x ^ 2 + y ^ 2 + z ^ 2)) + (z * x / (2 * y ^ 2 + z ^ 2 + x ^ 2)) + (x * y / (2 * z ^ 2 + x ^ 2 + y ^ 2)) - 3 / 4 ≤ 0 := by
    have h5 : 0 < (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) := by
      positivity
    have h6 : (y * z / (2 * x ^ 2 + y ^ 2 + z ^ 2)) + (z * x / (2 * y ^ 2 + z ^ 2 + x ^ 2)) + (x * y / (2 * z ^ 2 + x ^ 2 + y ^ 2)) - 3 / 4 = ( (y * z) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) + (z * x) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) + (x * y) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) - 3 / 4 * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) ) / ( (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) ) := by
      field_simp
      ring
    rw [h6] at *
    have h7 : ( (y * z) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) + (z * x) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) + (x * y) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) - 3 / 4 * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) ) ≤ 0 := by
      nlinarith [ sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]
    have h8 : ( (y * z) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) + (z * x) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) + (x * y) * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) - 3 / 4 * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) ) / ( (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      all_goals positivity
    linarith
  linarith