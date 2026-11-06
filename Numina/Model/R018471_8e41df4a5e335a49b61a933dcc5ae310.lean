import Mathlib

theorem algebra_162014 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y = x * y) (h2 : x + y + z = x * y * z) :
    1 < z ∧ z ≤ 4 / 3 := by
  have h3 : 1 < z := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), mul_pos hx hy]
  have h4 : z ≤ 4 / 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 4 / 3), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor <;> linarith [h3, h4]