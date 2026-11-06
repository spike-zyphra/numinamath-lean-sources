import Mathlib
theorem algebra_9365 {x y : ℝ} (h1 : x + y - 2 = 0) (h2 : x - y + 4 = 0)
    (h3 : 3 * x - 2 * y + 4 = 0) :
    3 * x - 2 * y + 9 = 0 := by
  have h4 : x = -1 := by
    linarith
  have h5 : y = 3 := by
    rw [h4] at h1
    linarith
  rw [h4, h5] at h3
  linarith