import Mathlib

theorem inequalities_600975 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = x * y * z) :
    x ^ 2 + y ^ 2 + z ^ 2 - 2 * (x * y + y * z + z * x) + 9 ≥ 0 := by 
  nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - x - z), sq_nonneg (z - x - y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
]