import Mathlib

theorem inequalities_602747 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y * z * (x + 2) * (y + 2) * (z + 2) ≤
    ((1 + 2 * (x * y + y * z + z * x) / 3) ^ 3) := by 
  have h1 : 0 < x * y * z := by positivity
  have h4 : x * y * z * (x + 2) * (y + 2) * (z + 2) ≤ (1 + 2 * (x * y + y * z + z * x) / 3) ^ 3 := by
    nlinarith [sq_nonneg (x * y * z - 1), sq_nonneg (x * y + y * z + z * x - 3), 
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
      mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith), 
      mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < z * x from mul_pos hz hx)
    ]
  linarith