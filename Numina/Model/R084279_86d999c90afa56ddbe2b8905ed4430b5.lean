import Mathlib

theorem algebra_177275 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x * 2 = y) (h2 : y * 3 = z) (h3 : x * 27 = z * 17) :
    x = 9 := by 
  nlinarith