import Mathlib

theorem algebra_290924 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x = y / 2) (h2 : x + 30 = 3 * y) :
    x = 6 := by
  have eq1 : y = 12 := by
    linarith [h1, h2]
  have hx6 : x = 6 := by
    rw [eq1] at h1
    linarith
  exact hx6