import Mathlib

theorem algebra_199472 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : 1 / x + 1 / y = 1 / 30) (h2 : 1 / x + 1 / z = 1 / 42) (h3 : 1 / y + 1 / z = 1 / 35) :
    1 / x + 1 / y + 1 / z = 1 / (23 + 1 / 3) := by
  have eq1 : 1 / x + 1 / y + 1 / z = (1 / 30 + 1 / 42 + 1 / 35) / 2 := by
    linarith
  rw [eq1]
  norm_num