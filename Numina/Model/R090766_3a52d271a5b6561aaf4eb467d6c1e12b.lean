import Mathlib

theorem algebra_197621
  (x y z : ℝ)
  (hx : 0 < x)
  (hy : 0 < y)
  (hz : 0 < z)
  (h1 : x^2 + x * y + y^2 = 27)
  (h2 : y^2 + y * z + z^2 = 9)
  (h3 : z^2 + x * z + x^2 = 36) :
  x * y + y * z + x * z = 18:= by
  nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z)
          ]