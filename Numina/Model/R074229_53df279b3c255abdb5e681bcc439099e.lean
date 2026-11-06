import Mathlib
open Real

theorem algebra_3218 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x = 2 * y) (h2 : x - y = 5) :
    y = 5 := by
  rw [h1] at h2
  linarith