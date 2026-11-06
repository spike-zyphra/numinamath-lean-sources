import Mathlib

open Real Set

theorem algebra_315155 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (x + 1) * (y + 1) * (z + 1) ≥ 8 := by

  have h1 : (x + 1) * (y + 1) * (z + 1) = 2 + (x * y + x * z + y * z) + (x + y + z) := by
    have h1 : x * y * z = 1 := hxyz
    calc
    (x + 1) * (y + 1) * (z + 1) = x * y * z + (x * y + x * z + y * z) + (x + y + z) + 1 := by ring
    _ = 1 + (x * y + x * z + y * z) + (x + y + z) + 1 := by rw [h1]
    _ = 2 + (x * y + x * z + y * z) + (x + y + z) := by ring
  rw [h1]

  have h2 : x + y + z ≥ 3 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h3 : x * y + x * z + y * z ≥ 3 := by
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, hxyz]

  nlinarith