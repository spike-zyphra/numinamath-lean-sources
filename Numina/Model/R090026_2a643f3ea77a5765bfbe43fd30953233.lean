import Mathlib

theorem algebra_16546 {x y z : ℝ} (hx : x = -3) (hy : y = 5) (hz : z = -4) :
    x^2 + y^2 - z^2 + 2 * x * y = -12 := by
  rw [hx, hy, hz]
  norm_num