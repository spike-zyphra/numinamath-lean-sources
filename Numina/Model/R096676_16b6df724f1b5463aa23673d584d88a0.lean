import Mathlib

theorem algebra_142637 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x + y = 315) (h2 : (1 + 40 / 100) * (x + y) = (1 + 25 / 100) * x + (1 + 50 / 100) * y) :
    x = 126 := by
  have h3 : y = 315 - x := by linarith
  rw [h3] at h2
  linarith