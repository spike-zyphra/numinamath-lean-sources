import Mathlib

theorem inequalities_3916 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * (y + z) / (x + y) ^ 2 + y * (z + x) / (y + z) ^ 2 +
    z * (x + y) / (z + x) ^ 2 ≥ 2 * x * y / ((x + y) * (y + z)) +
    2 * y * z / ((y + z) * (z + x)) + 2 * x * z / ((z + x) * (x + y)) := by
  have h1 : 0 < x * y * z := by
    positivity
  have h4 : 0 < (x + y) * (y + z) * (z + x) := by
    positivity
  have h8' :  x * (y + z) / (x + y) ^ 2 + y * (z + x) / (y + z) ^ 2 + z * (x + y) / (z + x) ^ 2 - (2 * x * y / ((x + y) * (y + z)) + 2 * y * z / ((y + z) * (z + x)) + 2 * x * z / ((z + x) * (x + y))) =
      (x * (y + z) * (y + z) ^ 2 * (z + x) ^ 2 + y * (z + x) * (x + y) ^ 2 * (z + x) ^ 2 + z * (x + y) * (x + y) ^ 2 * (y + z) ^ 2 - 
      2 * x * y * (x + y) * (y + z) * (z + x) ^ 2 - 2 * y * z * (x + y) ^ 2 * (y + z) * (z + x) - 2 * x * z * (x + y) * (y + z) ^ 2 * (z + x)
      ) / ((x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2) := by
    field_simp
    ring
  have h8 : (x * (y + z) / (x + y) ^ 2 + y * (z + x) / (y + z) ^ 2 + z * (x + y) / (z + x) ^ 2 ) - (2 * x * y / ((x + y) * (y + z)) + 2 * y * z / ((y + z) * (z + x)) + 2 * x * z / ((z + x) * (x + y))) ≥ 0 := by
    rw [h8']
    apply div_nonneg
    nlinarith [sq_nonneg (x * (y + z) - y * (x + y)), sq_nonneg (y * (z + x) - z * (y + z)), sq_nonneg (z * (x + y) - x * (z + x)), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (y + z)), sq_nonneg (y * (z + x)), sq_nonneg (z * (x + y)), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz), 
          mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < z * x from mul_pos hz hx), 
          mul_pos (show 0 < y * z from mul_pos hy hz) (show 0 < z * x from mul_pos hz hx)
      ]
    positivity
  linarith [h8]