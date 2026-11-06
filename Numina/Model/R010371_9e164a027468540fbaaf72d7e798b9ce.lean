import Mathlib

theorem algebra_11307 {w : ℝ} (h : (w + 13)^2 = (3 * w + 7) * (2 * w + 4)) :
    w^2 = 28.2 := by
  have eq1 : (w + 13) ^ 2 = w^2 + 26 * w + 169 := by
    ring
  have eq2 : (3 * w + 7) * (2 * w + 4) = 6 * w^2 + 26 * w + 28 := by
    ring
  rw [eq1, eq2] at h
  have h1 : 5 * w ^ 2 = 141 := by
    linarith
  have hw2 : w^2 = (141 : ℝ) / 5 := by
    linarith
  rw [hw2]
  norm_num