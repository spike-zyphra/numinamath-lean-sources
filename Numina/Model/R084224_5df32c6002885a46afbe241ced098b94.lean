import Mathlib

theorem algebra_196301
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 75)
    (h2 : y^2 + y * z + z^2 = 64)
    (h3 : z^2 + x * z + x^2 = 139) :
    x * y + y * z + x * z = 80 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z), sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (-x + y + z)]