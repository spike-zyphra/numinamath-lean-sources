import Mathlib

theorem algebra_320453 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^3 - y^3 - z^3 = 3 * x * y * z) (h2 : x^2 = 2 * (y + z)) :
    x * y + y * z + z * x = 5 := by
  have h3 : x ≤ 5 := by
    nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - z),
      pow_two_nonneg (x + y + z), pow_two_nonneg (x - y - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h4 : y ≤ 5 := by
    nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - z),
      pow_two_nonneg (x + y + z), pow_two_nonneg (x - y - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h5 : z ≤ 5 := by
    nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - z),
      pow_two_nonneg (x + y + z), pow_two_nonneg (x - y - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  interval_cases x <;> interval_cases y <;> interval_cases z
    <;> omega