import Mathlib

theorem algebra_4899 (x y z p : ℝ) (h1 : p = (x + y + z) / 3) (h2 : p + x = 19) (h3 : p + y = 22) (h4 : p + z = 37) : p = 13 := by
  have hx : x = 19 - p := by linarith
  have hy : y = 22 - p := by linarith
  have hz : z = 37 - p := by linarith
  rw [hx, hy, hz] at h1
  linarith