import Mathlib

theorem algebra_252772 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    (x + y) * (x + z) ≥ 2 := by
  have h1 : (x + y) * (x + z) = x * (x + y + z) + y * z := by
    ring
  have h2 : y * z > 0 := by nlinarith [hy, hz]
  have h3 : x * (x + y + z) > 0 := by
    apply mul_pos
    linarith
    nlinarith [hx, hy, hz]
  have h4 : x * (x + y + z) + y * z ≥ 2 := by
    nlinarith [sq_nonneg (x * (x + y + z) - 1), sq_nonneg (y * z - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h]
  rw [h1]
  linarith