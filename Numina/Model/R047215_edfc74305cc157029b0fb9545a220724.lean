import Mathlib

theorem inequalities_600844 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = x * y * z) :
    x * (1 - y ^ 2) * (1 - z ^ 2) + y * (1 - z ^ 2) * (1 - x ^ 2) +
    z * (1 - x ^ 2) * (1 - y ^ 2) ≥ 12 * Real.sqrt 3 := by 
  have h2 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  have h1 : x * y * z ≥ 3 * Real.sqrt 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (mul_pos hx hy) hz, sq_nonneg (x * y * z), sq_nonneg (x + y + z - 3 * Real.sqrt 3), sq_nonneg (x * y * z - 3 * Real.sqrt 3)
         ]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (mul_pos hx hy) hz, h1, 
          sq_nonneg (x ^ 2 * y ^ 2 * z ^ 2 - 27), sq_nonneg (x * y * z - 3 * Real.sqrt 3), h2, sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x * y * z ^ 2 - x * y ^ 2 * z), sq_nonneg (x * y * z ^ 2 - x ^ 2 * y * z), sq_nonneg (x ^ 2 * y * z - x * y ^ 2 * z)
          ]