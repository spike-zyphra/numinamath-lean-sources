import Mathlib

theorem inequalities_202556 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    x * y * z * (x + y + z) ≤ 1 / 3 := by
  have h1 : x * y + y * z + z * x = 1 := h
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz), mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < z * x from mul_pos hz hx) ]