import Mathlib

theorem algebra_16083 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (x * y) + z = (x + z) * (y + z)) :
    x * y * z ≤ 1 / 27 := by
  have h1 : x + y + z = 1 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
          h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]