import Mathlib

theorem algebra_138404 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 3) (h2 : y^2 + z^2 + y * z = 4) (h3 : z^2 + x^2 + z * x = 7) :
    x + y + z = Real.sqrt 13 := by 
  have h : (x + y + z) ^ 2 = 13 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  rw [show x + y + z = Real.sqrt ((x + y + z) ^ 2) by
    rw [Real.sqrt_sq (by nlinarith)]]
  rw [h]