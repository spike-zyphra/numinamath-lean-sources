import Mathlib

theorem algebra_321795 (x y z : ℝ) (hx : x = 2 + 1 / 5) (hy : y = -5 / 11) (hz : z = -(2 + 1 / 5)) :
  x ^ 2 + x * z+ 2 * y * z + 3 * x + 3 * z + 4 * x * y + 5 = 3 := by
  rw [hx] at *
  rw [hy] at *
  rw [hz] at *
  norm_num