import Mathlib

theorem algebra_596938 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 2*x*y*z = 3*x^2 + 4*y^2 + 5*z^2) :
    3*x + 2*y + z ≥ 36 := by 
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (z - 6),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - 36), sq_nonneg (y * z - 36), sq_nonneg (x * z - 36),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]