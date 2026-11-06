import Mathlib

theorem algebra_18566 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y = 24) (h2 : x * z = 48) (h3 : y * z = 72) :
    x + y + z = 22 := by
  nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]