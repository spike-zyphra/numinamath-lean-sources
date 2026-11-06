import Mathlib

theorem inequalities_45118 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    x * y * z * (x + y + z) + 2021 ≥ 2024 * x * y * z := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - 3), sq_nonneg (x * y * z - 1), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz,
          h, mul_pos (show 0 < x * y by nlinarith) (show 0 < z by linarith)]