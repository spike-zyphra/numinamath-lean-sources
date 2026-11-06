import Mathlib

theorem algebra_288777 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : y = x * 1.4) (h2 : z = y * 1.25) (h3 : x = 2 * z) :
    x / z = 1 / 2 := by 
  have eq1 : z = x * 1.75 := by
    rw [h2, h1]
    ring
  have eq2 : x = 0 := by
    nlinarith [h3, eq1]
  linarith [hx, eq2]