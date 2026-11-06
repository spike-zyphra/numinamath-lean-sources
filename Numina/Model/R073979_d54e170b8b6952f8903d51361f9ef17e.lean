import Mathlib

theorem algebra_197203 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 12) (h2 : y^2 + y * z + z^2 = 25) (h3 : z^2 + x * z + x^2 = 37) :
    x * y + y * z + x * z = 20 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]