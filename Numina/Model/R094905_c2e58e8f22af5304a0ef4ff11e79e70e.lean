import Mathlib

theorem algebra_167218
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x + y + x * y = 8)
    (h2 : y + z + y * z = 15)
    (h3 : z + x + z * x = 35) :
    x + y + z + x * y = 15 := by
  nlinarith [sq_nonneg (x - 7 / 2), sq_nonneg (y - 1), sq_nonneg (z - 7),
    h1, h2, h3, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]