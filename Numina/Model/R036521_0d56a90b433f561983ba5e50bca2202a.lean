import Mathlib

theorem algebra_22183 {x y : ℝ} (h : abs (x + y - 7) + abs (4 * x - y + 12) = 0) :
    (x, y) = (-1, 8) := by
  have h1 : abs (x + y - 7) = 0 := by
    linarith [abs_nonneg (x + y - 7), abs_nonneg (4 * x - y + 12)]
  have h2 : abs (4 * x - y + 12) = 0 := by
    linarith [abs_nonneg (x + y - 7), abs_nonneg (4 * x - y + 12)]
  have h3 : x + y - 7 = 0 := by
    rwa [abs_eq_zero] at h1
  have h4 : 4 * x - y + 12 = 0 := by
    rwa [abs_eq_zero] at h2
  have hx : x = -1 := by
    linarith [h3, h4]
  have hy : y = 8 := by
    linarith [h3, hx]
  simp [Prod.ext_iff, hx, hy]