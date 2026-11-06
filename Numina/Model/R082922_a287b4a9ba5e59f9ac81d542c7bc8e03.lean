import Mathlib

theorem algebra_176707 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x + y + z = 150) (h2 : y + z = 250) (h3 : x = 30 / 100 * (x + y + z)) :
    z = 170 := by
  linarith