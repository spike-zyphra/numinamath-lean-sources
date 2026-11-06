import Mathlib

theorem algebra_6470 (x y : ℝ) (h : abs (3 * x - 2 * y + 16) + abs (5 - y) = 0) :
    x = -2 := by
  have h1 : abs (3 * x - 2 * y + 16) = 0 := by 
    linarith [abs_nonneg (3 * x - 2 * y + 16), abs_nonneg (5 - y)]
  have h2 : abs (5 - y) = 0 := by 
    linarith [abs_nonneg (3 * x - 2 * y + 16), abs_nonneg (5 - y)]
  have hy : y = 5 := by 
    rw [abs_eq_zero] at h2
    linarith
  have h3 : 3 * x - 2 * y + 16 = 0 := by 
    rw [abs_eq_zero] at h1
    linarith
  rw [hy] at h3
  linarith