import Mathlib

theorem algebra_234636 (d : ℝ) (h : d = 30) (h1 : 600 * t > 550 * t + d) :
    t > 75 / 165 := by
  rw [h] at h1
  linarith