import Mathlib

theorem algebra_197861
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 48)
    (h2 : y^2 + y * z + z^2 = 9)
    (h3 : z^2 + x * z + x^2 = 57) :
    x * y + y * z + x * z = 24 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]