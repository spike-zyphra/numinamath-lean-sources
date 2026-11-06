import Mathlib

theorem algebra_274799 (n : ℝ) (hn : n > 0) (h : √(4 * n^2) = 64) : n = 32 := by
  have h2 : √(4 * n^2) = 2 * n := by
    have h3 : (4 * n^2 : ℝ) = (2 * n) ^ 2 := by ring
    rw [h3]
    rw [Real.sqrt_sq]
    all_goals linarith
  rw [h2] at h
  linarith