import Mathlib

theorem algebra_3416 {x y : ℝ} (h : abs (x + 3) = -(abs (y - 6))) : abs (x - y) = 9 := by
  have h1 : abs (x + 3) = 0 := by
    linarith [abs_nonneg (x + 3), abs_nonneg (y - 6)]
  have hx : x = -3 := by
    rw [abs_eq_zero] at h1
    linarith
  have h2 : abs (y - 6) = 0 := by
    linarith [abs_nonneg (x + 3), abs_nonneg (y - 6), h]
  have hy : y = 6 := by
    rw [abs_eq_zero] at h2
    linarith
  rw [hx, hy]
  norm_num