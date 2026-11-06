import Mathlib

theorem algebra_93658 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(hxy : x * y = 24) (hxz : x * z = 48) (hyz : y * z = 72) :
x + y + z = 22 := by
  have h1 : z = 2 * y := by
    nlinarith [hxy, hxz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h2 : y = 6 := by
    rw [h1] at hyz
    nlinarith [sq_pos_of_pos hy, sq_nonneg (y - 6)]

  have h3 : z = 12 := by
    rw [h2] at h1
    linarith

  have h4 : x = 4 := by
    rw [h2] at hxy
    nlinarith

  linarith [h4, h2, h3]