import Mathlib

theorem algebra_232165 (x y z a : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y - z = a) (h2 : y * z - x = a) (h3 : z * x - y = a) :
    a ≥ -1 / 4 := by
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]