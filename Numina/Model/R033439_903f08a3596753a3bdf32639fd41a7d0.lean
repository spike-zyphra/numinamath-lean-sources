import Mathlib

theorem algebra_607160 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (2 * x ^ 2 + y * z) * (2 * y ^ 2 + x * z) * (2 * z ^ 2 + x * y) = 26 * x ^ 2 * y ^ 2 * z ^ 2) :
    False := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
      sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
      sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith),
      mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith),
      mul_pos (show 0 < x * z by nlinarith) (show 0 < y * z by nlinarith),
      mul_pos (show 0 < x by linarith) (show 0 < y * z by nlinarith)
  ]