import Mathlib

theorem algebra_269636 (x : ℝ) (h : x ≠ 0) (h1 : 2 * x * 3 = 450) (h2 : 7 * x * y = 2100) :
    y = 4 := by
  have hx : x = 75 := by
    linarith
  rw [hx] at h2
  have hy : y = 4 := by
    nlinarith
  exact hy