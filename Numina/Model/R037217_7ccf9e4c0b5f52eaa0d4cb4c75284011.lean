import Mathlib

theorem inequalities_69293 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) *
    (x * y + y * z + z * x) ≥ 3 * (x + y + z) ^ 2 * (x * y * z) ^ 2 := by 
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) * (x * y + y * z + z * x) - 
      3 * (x + y + z) ^ 2 * (x * y * z) ^ 2 ≥ 0 := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), 
            sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
            mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
            mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)]
  linarith