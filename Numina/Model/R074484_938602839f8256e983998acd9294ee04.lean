import Mathlib

theorem algebra_178619 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 1 = y * 2) (h2 : y * 1 = x * 2 + z) (hz : z > 0)
    (h3 : z * 1 = x * 2 + y) :
    x = 1.333 := by
  nlinarith